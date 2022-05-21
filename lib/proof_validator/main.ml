open Containers

module StringMap = Map.Make(String)

let split_last =
  let rec loop (acc, last) = function
    | [] -> List.rev acc, last
    | h :: t -> loop (last :: acc, h) t in
  function
  | [] -> None
  | h :: t -> Some (loop ([], h) t)

let data = Proof_validator.Verification_condition.{
  poly_vars = ["A"];
  functions= [("TLC.LibList.app", Lang.Type.Forall (["A"], [List (Var "A"); List (Var "A"); List (Var "A")]));
    ("TLC.LibList.rev", Lang.Type.Forall (["A"], [List (Var "A"); List (Var "A")]));
    ("TLC.LibListZ.length", Lang.Type.Forall (["A"], [List (Var "A"); Int]));
    ("TLC.LibListZ.make", Lang.Type.Forall (["A"], [Int; Var "A"; List (Var "A")]))];
  invariant = ("I", [List (Var "A"); Int]);
  (* define fresh variables + make env map for  *)
  env =
    [("l", List (Var "A")); ("s", Func); ("v", Loc); ("tmp", Val);
     ("len", Var "Coq.Numbers.BinNums.Z"); ("ls", List (Var "A")); ("init", Var "A");
     ("rest", List (Var "A")); ("a", Array (Var "A")); ("data", List (Var "A"));
     ("idx", Var "Coq.Numbers.BinNums.Z"); ("tmp0", Val)];
  (* evaluate and assert equalities for all assumptions *)
  assumptions =
    [(List (Var "A"), `Var "ls", `Constructor ("::", [`Var "init"; `Var "rest"]));
     (Product [Int; List (Var "A")],
      `Tuple [`Var "len"; `Constructor ("::", [`Var "init"; `Var "rest"])],
      `Tuple [`App ("TLC.LibListZ.length", [`Var "l"]); `App ("TLC.LibList.rev", [`Var "l"])]);
     (List (Var "A"), `Constructor ("::", [`Var "init"; `Var "rest"]), `App ("TLC.LibList.rev", [`Var "l"]));
     (Int, `Var "len", `App ("TLC.LibListZ.length", [`Var "l"]));
     (List (Var "A"), `Var "data", `App ("TLC.LibListZ.make", [`Var "len"; `Var "init"]));
     (Int, `Var "idx", `App ("-", [`Var "len"; `Int 2]))];

  (* user provides input expression (Expr.t list -> Expr.t) & (Expr.t list -> Expr.t array)  *)
  initial = { expr_values = [|`Var "data"|]; param_values = [`Constructor ("[]", []); `Var "idx"] };

  conditions =
    [
      (* define fresh variables + make env map for qf *)
      { qf =
         [("r", List (Var "A")); ("t", List (Var "A")); ("v", Var "A"); ("acc", Int)];
        (* evaluate and assert equalities for assumptions *)
       assumptions = [`Eq ((List (Var "A"),
                            `Var "rest",
                            `App ("TLC.LibList.app", [`Var "t"; `Constructor ("::", [`Var "v"; `Var "r"])])))];
        (* param values *)
       param_values = [`Var "t"; `Var "acc"];

       post_param_values = [
         `App ("TLC.LibList.app",
               [`Var "t"; `Constructor ("::", [`Var "v"; `Constructor ("[]", [])])]);
         `App ("-", [`Var "acc"; `Int 1])
       ];
       expr_values = [|fun exp -> `App ("Array.set", [(`App ("CFML.WPArray.Array", [exp])); `Var "acc"; `Var "v"])|] }
    ]
} 

type ctx = {
  ctx: Z3.context;
  solver: Z3.Solver.solver;
  int_sort: Z3.Sort.sort;
  poly_var_map: (string, Z3.Sort.sort) Hashtbl.t;
  type_map: (Lang.Type.t, Z3.Sort.sort) Hashtbl.t;
  fun_map: (string, (Lang.Type.t list * Z3.FuncDecl.func_decl) list) Hashtbl.t
}

type env = {
  types: Lang.Type.t StringMap.t;
  values: Z3.Expr.expr StringMap.t;
}

type t = {
  ctx: ctx;
}

let rec typeof env (expr: Lang.Expr.t) : Lang.Type.t option =
  (match expr with
   | `Tuple elts ->
     List.all_some (List.map (typeof env) elts)
     |> Option.map (fun tys -> Lang.Type.Product tys)
   | `Var v -> StringMap.find_opt v env

   | `Lambda _ -> None
   | `Int _ -> Some Lang.Type.Int
   | `App ("-", _) -> Some Lang.Type.Int
   | `App ("+", _) -> Some Lang.Type.Int
   | `Constructor ("[]", []) -> None
   | `Constructor ("::", [h; t]) ->
     Option.choice [
       typeof env h |> Option.map (fun ty -> Lang.Type.List ty);
       typeof env t
     ]
   | `App (_, _) -> None
   | `Constructor _ -> None
  )

let rec eval_type (ctx: ctx) (ty: Lang.Type.t) : Z3.Sort.sort =
  Hashtbl.get_or_add ctx.type_map ~k:ty ~f:(fun ty ->
    match ty with
    | Unit -> Z3.Sort.mk_uninterpreted ctx.ctx (Z3.Symbol.mk_string ctx.ctx "unit")
    | Var "Coq.Numbers.BinNums.Z" -> ctx.int_sort
    | Int -> ctx.int_sort
    | Var v -> begin match Hashtbl.find_opt ctx.poly_var_map v with
      | Some s -> s
      | None -> failwith (Format.sprintf "found unknown type variable %s" v)
      end
    | List ity ->
      let sort = eval_type ctx ity in
      Z3.Z3List.mk_list_s ctx.ctx (Lang.Type.show ty) sort
    | Product elts ->
      Z3.Tuple.mk_sort ctx.ctx
        Z3.Symbol.(mk_string ctx.ctx (Lang.Type.show ty))
        (List.mapi (fun ind _ -> Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "get(%s)(%d)" (Lang.Type.show ty) ind)
           elts)
        (List.map (eval_type ctx) elts)
    | Array _
    | Ref _ 
    | Loc
    | ADT (_, _, _) 
    | Val 
    | Func ->
      Format.printf "treating to type %s as opaque Z3 sort@." (Lang.Type.show ty);
      Z3.Sort.mk_uninterpreted_s ctx.ctx ((Lang.Type.show ty))
  )

let rec eval_expr ?(ty: Lang.Type.t option)
      (ctx: ctx)
      (env: env)
      (expr: Lang.Expr.t) =
  match expr, Option.or_lazy ~else_:(fun () -> typeof env.types expr) ty with
  | (`Var name, _) ->
    StringMap.find_opt name env.values
    |> Option.get_exn_or (Printf.sprintf "found unknown variable %s" name)
  | (`Int n, _) ->
    Z3.Arithmetic.Integer.mk_numeral_i ctx.ctx n
  | (`Tuple exprs, ty) ->
    let ty = ty |> Option.get_exn_or (Format.sprintf "could not type tuple %s" (Lang.Expr.show expr)) in
    let sort = eval_type ctx ty in
    let mk = Z3.Tuple.get_mk_decl sort in
    let exprs =
      begin match ty with
      | Product elts -> List.combine exprs (List.map Option.some elts) |> List.to_iter
      | _ -> List.to_iter exprs |> Iter.map (Fun.flip Pair.make None)
      end |> Iter.map (fun (expr, ty) -> eval_expr ?ty ctx env expr)
      |> Iter.to_list in
    Z3.FuncDecl.apply mk exprs
  | (`App ("+", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_add ctx.ctx [l;r]
  | (`App ("-", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_sub ctx.ctx [l;r]
  | (`App (fname, args), _) ->
    begin match Hashtbl.find ctx.fun_map fname with
    | [_, fapp] ->
      let args = List.map (eval_expr ctx env) args in
      Z3.Expr.mk_app ctx.ctx fapp args
    | _ ->
      failwith (Format.sprintf
                  "found multiple polymorphic instantiations for function %s (not supported atm)"
                  fname)
    end
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types h) ->
    let ty = Lang.Type.List (typeof env.types h |> Option.get_exn_or "invalid type") in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h = eval_expr ctx env h in
    let t = eval_expr ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types t) ->
    let ty = typeof env.types t |> Option.get_exn_or "invalid type" in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h = eval_expr ctx env h in
    let t = eval_expr ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), Some ty) ->
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h = eval_expr ctx env h in
    let t = eval_expr ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("[]", []), Some ty) ->
    let nil = Z3.Z3List.get_nil_decl (Hashtbl.find ctx.type_map ty) in
    Z3.Expr.mk_app ctx.ctx nil []
  | (`Lambda _, _)
  | (`Constructor _, _) -> failwith (Format.sprintf "attempt to convert unsupported expression %s to Z3"
                                       (Lang.Expr.show expr))

let embed (data: Proof_validator.Verification_condition.verification_condition) =
  let ctx = Z3.mk_context ["model", "false"; "proof", "false"; "timeout", "1000"] in
  let solver = Z3.Solver.mk_solver ctx None in
  Z3.Solver.set_parameters solver (
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") 1000;
    params
  );

  let poly_var_map = 
    List.map Fun.(Pair.dup_map @@ Z3.Sort.mk_uninterpreted ctx % Z3.Symbol.mk_string ctx) data.poly_vars
    |> Hashtbl.of_list in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in
  let ctx = {ctx; solver; int_sort; poly_var_map; type_map=Hashtbl.create 10; fun_map=Hashtbl.create 10} in
  let type_map = StringMap.of_list data.env in
  let env =
    data.env
    |> List.to_iter
    |> Iter.map Pair.(map_snd (eval_type ctx))
    |> Iter.map Fun.(Pair.dup_map @@ uncurry @@ Z3.Expr.mk_fresh_const ctx.ctx)
    |> Iter.map Pair.(map_fst fst)
    |> StringMap.of_iter in
  List.iter (fun (fname, Lang.Type.Forall (vars, sign)) ->
    let (let+) x f = List.(>>=) x f in
    let bindings = 
      let+ vars = List.map_product_l (fun v -> List.map Pair.(make v) data.poly_vars) vars in
      let fname = fname ^ "(" ^ String.concat "," (List.map snd vars) ^ ")" in
      let poly_binding =
        List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
        |> StringMap.of_list in
      let sign = List.map Lang.Type.(subst poly_binding) sign in
      let fname = Z3.Symbol.mk_string ctx.ctx fname in

      let sign = List.map (eval_type ctx) sign in
      let args, ret = split_last sign |> Option.get_exn_or "empty signature" in
      let fb = Z3.FuncDecl.mk_func_decl ctx.ctx fname args ret in
      [List.map (fun (_, v) -> Lang.Type.Var v) vars, fb] in
    Hashtbl.add ctx.fun_map fname bindings;
  ) data.functions;
  let env = {values=env; types=type_map} in
  let assumptions = 
  List.map (fun (ty, l, r) ->
    let l = eval_expr ~ty ctx env l in
    let r = eval_expr ~ty ctx env r in
    Z3.Boolean.mk_eq ctx.ctx l r
    ) data.assumptions in
  Z3.Solver.add solver assumptions;

  (* once Z3 context initialised, return a generator function that can be used to validate candidate expressions *)
  fun (gen_pred, gen_values) ->
    let (let-!) x f = match x with Some true -> f () | v -> Z3.Solver.pop solver 1; v in 
    let negate x = Z3.Boolean.mk_not ctx.ctx x in
    let check x = match Z3.Solver.check solver [x] with
        Z3.Solver.UNSATISFIABLE -> Some false
      | SATISFIABLE -> Some true
      | UNKNOWN -> None in
    let prove x = Option.map not @@ check (negate x) in
    let rec all_hold = function
      | [] -> Some true
      | h :: t ->
        match prove h with
        | Some true -> Z3.Solver.add solver [h]; all_hold t
        | v -> v in
    let rec iter f = function
      | [] -> Some true
      | h :: t ->
        match f h with
        | Some true -> iter f t
        | v -> v in
    Z3.Solver.push solver;
    (* check the initial predicate generated by the user *)
    let user_initial_pred = gen_pred data.initial.param_values
                            |> eval_expr ctx env in
    let-! () = prove user_initial_pred in
    Z3.Solver.add solver [user_initial_pred];
    let user_initial_values = gen_values data.initial.param_values |> Array.to_list in

    (* check initial values are equal to the expressions used to fill the holes by the user *)
    let-! () = 
      List.combine user_initial_values (Array.to_list data.initial.expr_values)
      |> List.map (fun (l, r) -> Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r))
      |> all_hold in

    (* for each remaining invariant verification condition  *)

    let-! () = iter (fun (vc: Proof_validator.Verification_condition.vc) ->
      Z3.Solver.push solver;
      let env = vc.qf
                |> List.fold_left (fun env (name, ty) ->
                  let sort = eval_type ctx ty in
                  {values = StringMap.add
                               name (Z3.Expr.mk_const_s ctx.ctx name sort)
                               env.values;
                    types = StringMap.add name ty env.types}
                ) env in
      let assumptions = 
        List.map (function
          | `Eq (ty, l, r) ->
            let l = eval_expr ~ty ctx env l in
            let r = eval_expr ~ty ctx env r in
            Z3.Boolean.mk_eq ctx.ctx l r
          | `Assert expr ->
            eval_expr ctx env expr
        ) vc.assumptions in
      Z3.Solver.add solver assumptions;
      (* user predicate holds with initial parameters *)
      let user_pre_pred = gen_pred vc.param_values |> eval_expr ctx env in
      Z3.Solver.add solver [user_pre_pred];

      (* 1st. check that implies predicate with post param values *)
      let user_post_pred = gen_pred vc.post_param_values |> eval_expr ctx env in
      let-! () = prove user_post_pred in
      Z3.Solver.add solver [user_post_pred];

      (* 2nd. check user generated post values (with post param values) are equal to
          user generated pre values symbolically evaluated *)
      let user_post_values = gen_values vc.post_param_values |> Array.to_list in
      let user_preval_values = 
        let user_pre_values = gen_values vc.param_values |> Array.to_list in
        List.combine user_pre_values (Array.to_list vc.expr_values)
        |> List.map (fun (expr, f) -> f expr) in
      let-! () =
        List.combine user_post_values user_preval_values
        |> List.map (fun (l,r) ->
          Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r)
        )
        |> all_hold in
      (* if all hold, then we good boys. *)
      Z3.Solver.pop solver 1;
      Some true
    ) data.conditions in

    Z3.Solver.pop solver 1;
    Some true


let () =
  let _ctx = embed data in
  print_endline "hello world"
