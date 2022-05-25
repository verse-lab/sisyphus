open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let should_print = ref false

exception Invalid of bool option * string

let () =
  Printexc.register_printer (function
      Failure msg -> Some msg
    | _ -> None
  )

let split_last =
  let rec loop (acc, last) = function
    | [] -> List.rev acc, last
    | h :: t -> loop (last :: acc, h) t in
  function
  | [] -> None
  | h :: t -> Some (loop ([], h) t)


let send_to_z3 query =
  if !should_print then
    print_endline query;
  let open Bos in
  OS.Cmd.run_io Cmd.(v "z3" % "-in") OS.Cmd.(in_string query)
  |> OS.Cmd.out_string
  |> Result.get_exn
  |> fst
  |> function
  | "sat" -> Some true
  | "unsat" -> Some false
  | "unknown" -> None
  | e -> failwith (Format.sprintf "unexpected output from z3 \"%s\"@.query:@.%s@." e query)

let check ?(timeout=10_000) solver expr =
  send_to_z3 (Format.sprintf {|
                (set-option :timeout %d)
                %s
                (assert %s)
                (check-sat)
|} timeout Z3.Solver.(to_string solver) Z3.Expr.(to_string expr)) 


let normalize =
  let update s =
    if String.prefix ~pre:"TLC.LibListZ." s
    then Some ("TLC.LibList." ^ String.drop (String.length "TLC.LibListZ.") s)
    else None in
  let update_expr e = Lang.Expr.subst_functions update e in
  let update_assertion = function
      `Eq (ty, l, r) ->
      `Eq (ty, update_expr l, update_expr r)
    | `Assert prop -> `Assert (update_expr prop) in
  fun (data: Proof_validator.Verification_condition.verification_condition) ->
    let functions =
      data.functions
      |> List.fold_map (fun fns (name, sg) ->
        let name = Option.value ~default:name @@ update name in
        if StringSet.mem name fns
        then (fns, None)
        else
          let fns = StringSet.add name fns in
          (fns, Some (name, sg))
      ) StringSet.empty
      |> snd
      |> List.filter_map Fun.id in

    let properties =
      List.map (fun (pname, (qfs, params, assums, concl)) ->
        let assums = List.map update_assertion assums in
        (pname, (qfs, params, assums, update_assertion concl))) data.properties in
    let assumptions =
      List.map (fun (ty, l, r) -> (ty, update_expr l, update_expr r)) data.assumptions in

    let initial : Proof_validator.Verification_condition.initial_vc =  {
      expr_values=Array.map update_expr data.initial.expr_values;
      param_values=List.map update_expr data.initial.param_values;
    } in
    let conditions = List.map (fun (vc: Proof_validator.Verification_condition.vc) ->
      {vc
       with param_values=List.map update_expr vc.param_values;
            assumptions=List.map update_assertion vc.assumptions;
            post_param_values=List.map update_expr vc.post_param_values;
            expr_values=Array.map (fun f -> fun e -> update_expr (f e)) vc.expr_values;
      }
    ) data.conditions in
    {data with
     functions;
     properties;
     assumptions;
     initial;
     conditions=conditions;
    }

type ctx = {
  ctx: Z3.context;
  solver: Z3.Solver.solver;
  int_sort: Z3.Sort.sort;
  poly_var_map: (string, Z3.Sort.sort) Hashtbl.t;
  update_map: (Lang.Type.t, Z3.FuncDecl.func_decl) Hashtbl.t;
  type_map: (Lang.Type.t, Z3.Sort.sort) Hashtbl.t;
  fun_map: (string, Lang.Type.t list * (Lang.Type.t list * Z3.FuncDecl.func_decl) list) Hashtbl.t
}

type env = {
  types: Lang.Type.t StringMap.t;
  values: Z3.Expr.expr StringMap.t;
}


let update_with_binding env name (vl,ty)  =
  {values = StringMap.add name vl env.values;
   types = StringMap.add name ty env.types}      

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
      let nil =
        Z3.Datatype.mk_constructor_s ctx.ctx
          (Format.sprintf "nil(%s)" (Lang.Type.show ty))
          (Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "is_nil(%s)" (Lang.Type.show ty))
          [] [] [] in
      let cons =
        Z3.Datatype.mk_constructor_s ctx.ctx
          (Format.sprintf "cons(%s)" (Lang.Type.show ty))
          (Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "is_cons(%s)" (Lang.Type.show ty))
          [
            (Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "head(%s)" (Lang.Type.show ty));
            (Z3.Symbol.mk_string ctx.ctx @@ Format.sprintf "tail(%s)" (Lang.Type.show ty))
          ] [ Some sort; None ] [0; 0] in
      let constructors = [nil; cons ] in
      let dt = Z3.Datatype.mk_sort_s ctx.ctx (Format.sprintf "list(%s)" @@ Lang.Type.show ty) constructors in
      dt
    (* Z3.Z3List.mk_list_s ctx.ctx (Lang.Type.show ty) sort *)
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
      Format.printf "treating type %s as opaque Z3 sort@." (Lang.Type.show ty);
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
  | (`App ("TLC.LibOrder.le", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_le ctx.ctx l r
  | (`App ("TLC.LibOrder.lt", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_lt ctx.ctx l r
  | (`App ("TLC.LibOrder.ge", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_ge ctx.ctx l r
  | (`App ("TLC.LibOrder.gt", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_gt ctx.ctx l r
  | (`App ("=", [l;r]), ty) ->
    let ty = Option.or_ ~else_:(Option.or_ ~else_:(typeof env.types l) (typeof env.types r)) ty in
    let l = eval_expr ?ty ctx env l in
    let r = eval_expr ?ty ctx env r in
    Z3.Boolean.mk_eq ctx.ctx l r
  | (`App ("+", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_add ctx.ctx [l;r]
  | (`App ("-", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Arithmetic.mk_sub ctx.ctx [l;r]
  | (`App ("TLC.LibList.length" as fname, [ls]), None) when Option.is_none (typeof env.types ls) ->
    let _, fdecls = Hashtbl.find ctx.fun_map fname in
    let pvar = List.hd (Hashtbl.keys_list ctx.poly_var_map) in
    let ty : Lang.Type.t = List (Var pvar) in
    let fdecl = List.Assoc.get_exn ~eq:(List.equal Lang.Type.equal)
                  [Var pvar] fdecls in
    Z3.Expr.mk_app ctx.ctx fdecl [(eval_expr ~ty ctx env ls)]
  | (`App ("Array.set", [`App ("CFML.WPArray.Array", [ls]);ind;vl]), ty)
  | (`App ("TLC.LibContainer.update", [ls;ind;vl]), ty) ->
    let ty =
      match ty with
      | Some (List ty) -> Some ty
      | _ ->
        Option.or_lazy ~else_:(fun () -> typeof env.types vl)
          (Option.bind (typeof env.types ls) (function (List ty) -> Some ty | _ -> None)) in
    let ty = Option.get_exn_or "could not extract type of update" ty in
    let fdecl = Hashtbl.find_opt ctx.update_map ty
                |> Option.get_exn_or (Format.sprintf "found application of update to unsupported type %s"
                                        (Lang.Type.show ty)) in
    Z3.Expr.mk_app ctx.ctx fdecl [
      eval_expr ~ty:(List ty) ctx env ls;
      eval_expr ~ty:Int ctx env ind;
      eval_expr ~ty ctx env vl;
    ]
  | (`App (fname, args), _) ->
    begin match Hashtbl.find ctx.fun_map fname with
    | args_tys, [ptys, fapp] ->
      let arg_ty_map =
        let tbl = Hashtbl.create 10 in
        List.combine args_tys args
        |> List.iter (fun (aty, arg) ->
          Option.iter (fun ty ->
            Hashtbl.add tbl aty ty
          ) (typeof env.types arg)
        );
        tbl in
      let args = List.map (fun (ty, arg) ->
        let ty = Hashtbl.find_opt arg_ty_map ty in
        eval_expr ?ty ctx env arg
      ) (List.combine args_tys args) in
      Z3.Expr.mk_app ctx.ctx fapp args
    | _ ->
      failwith (Format.sprintf
                  "found multiple polymorphic instantiations for function %s (not supported atm)"
                  fname)
    | exception e ->
      failwith (Format.sprintf
                  "found use of unknown function %s (error %s)" fname (Printexc.to_string e))
    end
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types h) ->
    let ty = Lang.Type.List (typeof env.types h |> Option.get_exn_or "invalid type") in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    let t = eval_expr ~ty ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env.types t) ->
    let ty = typeof env.types t |> Option.get_exn_or "invalid type" in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    let t = eval_expr ~ty ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), Some ty) ->
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let t = eval_expr ~ty ctx env t in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("[]", []), Some ty) ->
    let nil = Z3.Z3List.get_nil_decl (Hashtbl.find ctx.type_map ty) in
    Z3.Expr.mk_app ctx.ctx nil []
  | (`Constructor ("[]", []), None) ->
    let nil = Z3.Z3List.get_nil_decl (
      Hashtbl.find ctx.type_map (Lang.Type.List
                                   (Var (Hashtbl.keys ctx.poly_var_map |> Iter.head_exn))
                                )) in
    Z3.Expr.mk_app ctx.ctx nil []
  | (`Lambda _, _)
  | (`Constructor _, _) -> invalid_arg (Format.sprintf "attempt to convert unsupported expression %s to Z3"
                                          (Lang.Expr.show expr))

let eval_property ctx env valid_poly name (poly_vars, params, assumptions, concl) =
  List.map_product_l (fun v -> List.map Pair.(make v) valid_poly) poly_vars
  |> List.filter_map (fun vars ->
    try
      let ty_instantiation =
        List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
        |> StringMap.of_list in
      let env, params = List.fold_map (fun env (name, ty) ->
        let ty = Lang.Type.subst ty_instantiation ty in
        let sort = eval_type ctx ty in
        let var = Z3.Expr.mk_fresh_const ctx.ctx name sort in
        {types=StringMap.add name ty env.types;
         values=StringMap.add name var env.values}, var
      ) env params in
      let body =
        let assumptions' =
          List.map (function
              `Eq (ty, l, r) ->
              let ty = Lang.Type.subst ty_instantiation ty in
              let l = eval_expr ~ty ctx env l in
              let r = eval_expr ~ty ctx env r in
              Z3.Boolean.mk_eq ctx.ctx l r              
            | `Assert expr ->
              eval_expr ctx env expr
          ) assumptions
          |> Z3.Boolean.mk_and ctx.ctx in
        let concl =
          match concl with
          | `Eq (ty, l, r) ->
            let l = eval_expr ~ty ctx env l in
            let r = eval_expr ~ty ctx env r in
            Z3.Boolean.mk_eq ctx.ctx l r
          | `Assert b ->
            eval_expr ctx env b
        in
        if List.is_empty assumptions
        then concl
        else
          Z3.Boolean.mk_implies ctx.ctx
            assumptions'
            concl
      in
      let qf =
        if List.is_empty params
        then body
        else Z3.Quantifier.expr_of_quantifier @@
          Z3.Quantifier.mk_forall_const ctx.ctx params body None [] [] None None in
      Some qf
    with (Z3.Error _ | Invalid_argument _) as _e ->
      (* Format.printf "failed to evaluate %s: {|%s|}@." name (Printexc.to_string _e); *)
      None
  )

let eval_property_bound ctx env valid_poly name (poly_vars, params, assumptions, concl) =
  List.map_product_l (fun v -> List.map Pair.(make v) valid_poly) poly_vars
  |> List.filter_map (fun vars ->
    try
      let ty_instantiation =
        List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
        |> StringMap.of_list in
      let no_vars = ref 0 in
      let fresh () = let v = !no_vars in incr no_vars; v in
      let env, params = List.fold_map (fun env (name, ty) ->
        let ty = Lang.Type.subst ty_instantiation ty in
        let sort = eval_type ctx ty in
        let var = Z3.Quantifier.mk_bound ctx.ctx (fresh ()) sort in
        {types=StringMap.add name ty env.types;
         values=StringMap.add name var env.values}, (Z3.Symbol.mk_string ctx.ctx name, sort)
      ) env params in
      let body =
        let assumptions' =
          List.map (function
              `Eq (ty, l, r) ->
              let ty = Lang.Type.subst ty_instantiation ty in
              let l = eval_expr ~ty ctx env l in
              let r = eval_expr ~ty ctx env r in
              Z3.Boolean.mk_eq ctx.ctx l r              
            | `Assert expr ->
              eval_expr ctx env expr
          ) assumptions
          |> Z3.Boolean.mk_and ctx.ctx in
        let concl =
          match concl with
          | `Eq (ty, l, r) ->
            let l = eval_expr ~ty ctx env l in
            let r = eval_expr ~ty ctx env r in
            Z3.Boolean.mk_eq ctx.ctx l r
          | `Assert b ->
            eval_expr ctx env b
        in
        if List.is_empty assumptions
        then concl
        else
          Z3.Boolean.mk_implies ctx.ctx
            assumptions'
            concl
      in
      let qf =
        if List.is_empty params
        then body
        else
          let names, tys = List.split (List.rev params) in
          Z3.Quantifier.expr_of_quantifier @@
          Z3.Quantifier.mk_forall ctx.ctx tys names body None [] [] None None in
      Some qf
    with (Z3.Error _ | Invalid_argument _) as _e -> None
  )

let check_verification_condition ctx env prove solver
      (vc: Proof_validator.Verification_condition.vc)
      (gen_pred, gen_values) =
  let assert_holds expr =
    begin match prove expr with
    | Some true -> ()
    | v -> raise (Invalid (v,
                           Format.sprintf "recieved %a when proving %s" (Option.pp Bool.pp) v
                             (Z3.Expr.to_string expr)
                          ))
    end in

  print_endline "updating env with params:";
  (* update the env with params  *)
  let env = vc.qf
            |> List.fold_left (fun env (name, ty) ->
              let sort = eval_type ctx ty in
              update_with_binding env name ((Z3.Expr.mk_fresh_const ctx.ctx name sort), ty)
            ) env in
  print_endline "done!";
  print_endline "adding assumptions:";
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
  print_endline "done";

  print_endline "checking implies predicate with post_param values:";
  (* 1st. check that implies predicate with post param values *)
  let user_post_pred = gen_pred vc.post_param_values |> eval_expr ctx env in
  assert_holds user_post_pred;
  print_endline "holds!";
  Z3.Solver.add solver [user_post_pred];

  print_endline "checking generated post values:";
  (* 2nd. check user generated post values (with post param values) are equal to
     user generated pre values symbolically evaluated *)
  let user_post_values = gen_values vc.post_param_values |> Array.to_list in
  let user_preval_values = 
    let user_pre_values = gen_values vc.param_values |> Array.to_list in
    List.combine user_pre_values (Array.to_list vc.expr_values)
    |> List.map (fun (expr, f) -> f expr) in
  List.combine user_post_values user_preval_values
  |> List.map (fun (l,r) ->
    Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r)
  )
  |> List.iter assert_holds;
  print_endline "done!"

let solver_params ctx timeout =
  let params = Z3.Params.mk_params ctx in
  Z3.Params.add_int params (Z3.Symbol.mk_string ctx "timeout") timeout;
  (* Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "model") false;
   * Z3.Params.add_symbol params (Z3.Symbol.mk_string ctx "logic") (Z3.Symbol.mk_string ctx "ALL"); *)
  params


let embed (data: Proof_validator.Verification_condition.verification_condition) =
  let data = normalize data in
  let ctx = Z3.mk_context [ ] in
  Z3.Params.set_print_mode ctx Z3enums.PRINT_SMTLIB_FULL;
  let solver = Z3.Solver.mk_solver_t ctx (Z3.Tactic.mk_tactic ctx "default") in

  let params = solver_params ctx 150_000 in
  Z3.Solver.set_parameters solver params;

  (* print_endline @@ (Z3.Solver.get_param_descrs solver |> Z3.Params.ParamDescrs.to_string); *)

  let poly_var_map = 
    List.map Fun.(Pair.dup_map @@ Z3.Sort.mk_uninterpreted ctx % Z3.Symbol.mk_string ctx) data.poly_vars
    |> Hashtbl.of_list in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in

  let ctx = {ctx; solver; int_sort; poly_var_map;
             type_map=Hashtbl.create 10;
             fun_map=Hashtbl.create 10;
             update_map=Hashtbl.create 10; } in
  let type_map = StringMap.of_list data.env in

  List.iter (fun (name, sort) ->
    let fdecl = 
      Z3.FuncDecl.mk_fresh_func_decl ctx.ctx
        (Format.sprintf "TLC.LibContainer.update(%s)" name) [
        eval_type ctx (List (Var name));
        eval_type ctx (Int);
        eval_type ctx (Var name)
      ]  (eval_type ctx (List (Var name)) ) in
    Hashtbl.add ctx.update_map (Var name) fdecl
  ) (Hashtbl.to_list poly_var_map);


  List.iter (fun (fname, Lang.Type.Forall (vars, sign)) ->
    let (let+) x f = List.(>>=) x f in
    let param_tys = split_last sign |> Option.get_exn_or "unexpected func signature" |> fst in
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
    Hashtbl.add ctx.fun_map fname (param_tys, bindings);
  ) data.functions;

  let env = {values=StringMap.empty; types=type_map} in

  let env =
    {env with values= data.env
                      |> List.rev
                      |> List.to_iter
                      |> Iter.map Pair.(map_snd (eval_type ctx))
                      |> Iter.map Fun.(Pair.dup_map @@ uncurry @@ Z3.Expr.mk_fresh_const ctx.ctx)
                      |> Iter.map Pair.(map_fst fst)
                      |> StringMap.add_iter env.values} in

  let assumptions = 
    List.map (fun (ty, l, r) ->
      let l = eval_expr ~ty ctx env l in
      let r = eval_expr ~ty ctx env r in
      Z3.Boolean.mk_eq ctx.ctx l r
    ) data.assumptions in
  Z3.Solver.add solver assumptions;

  List.iter (fun (name, ((poly_vars, params, assumptions, concl) as p)) ->
    print_endline @@ "\t - adding " ^ name ;
    let qfs = eval_property_bound ctx env data.poly_vars name p in
    Z3.Solver.add solver qfs;
  ) begin data.properties end;

  (* once Z3 context initialised, return a generator function that can be used to validate candidate expressions *)
  fun (gen_pred, gen_values) ->
    Z3.Solver.push solver;
    (* added assumptions *)
    (* print_endline "pushing stack";
     * Z3.Solver.push solver;
     * print_endline "pushed"; *)
    let (let-!) x f = match x with Some true -> f () | v -> Z3.Solver.pop solver 1; v in 
    let negate x = Z3.Boolean.mk_not ctx.ctx x in
    let check ?timeout x =
      begin match timeout with
      | Some timeout ->
        Z3.Params.add_int params (Z3.Symbol.mk_string ctx.ctx "timeout") timeout;
        Z3.Solver.set_parameters solver params;
      | _ -> ()
      end;
      (* check ?timeout solver x *)
      (* Format.printf "Z3 model for %s is %s@." (Z3.Expr.to_string x) (Z3.Solver.to_string solver); *)
      Z3.Solver.set_parameters solver params;
      match Z3.Solver.check solver [x] with
        Z3.Solver.UNSATISFIABLE -> Some false
      | SATISFIABLE -> Some true
      | UNKNOWN -> None in
    let prove x =
      if !should_print then begin
        Format.printf "Z3MODEL\n==================================\n%s\n(assert %s)\n(check-sat)\n@."
          (Z3.Solver.to_string solver) (Z3.Expr.to_string (negate x));
      end;
      Option.map not @@ check (negate x) in

    let rec all_hold = function
      | [] -> Some true
      | h :: t ->
        match prove h with
        | Some true -> Z3.Solver.add solver [h]; all_hold t
        | v -> v in

    (* check the initial predicate generated by the user *)
    let user_initial_pred =
      let init_values =
        List.combine (snd data.invariant) (data.initial.param_values)
        |> List.mapi (fun ind (ty, expr) ->
          Format.printf "__sisyphyus_var_%d = %a" ind Lang.Expr.pp expr;
          Format.sprintf "__sisyphyus_var_%d" ind, eval_expr ~ty ctx env expr) in
      let params = List.map (fun (name, _) -> `Var name) init_values in
      let env = {env with values=StringMap.add_list env.values init_values} in
      gen_pred params
      (* |> (fun x -> Format.printf "generated predicate was %a@." Lang.Expr.pp x; x) *)
      |> eval_expr ctx env in
    print_endline "proving initial predicate...";
    let-! () = prove user_initial_pred in
    print_endline "proved";
    Z3.Solver.add solver [user_initial_pred];
    let user_initial_values = gen_values data.initial.param_values |> Array.to_list in

    (* check initial values are equal to the expressions used to fill the holes by the user *)
    print_endline "proving equality of initial terms...";
    let-! () = 
      List.combine user_initial_values (Array.to_list data.initial.expr_values)
      |> List.map (fun (l, r) -> Z3.Boolean.mk_eq ctx.ctx (eval_expr ctx env l) (eval_expr ctx env r))
      |> all_hold in
    print_endline "proved";

    (* clear the context *)
    (* Z3.Solver.pop solver 1; *)
    let params = solver_params ctx.ctx 150_000 in
    Z3.Solver.set_parameters solver params;


    try
      (* for each remaining invariant verification condition  *)
      begin Fun.flip List.iter data.conditions @@ fun vc ->
        (* re-init the solver *)
        Z3.Solver.push solver;
        check_verification_condition ctx env prove solver vc (gen_pred, gen_values);
        Z3.Solver.pop solver 1;
      end;
      Some true
    with
    | Invalid (res, reason) ->
      Format.eprintf "failed to prove correctness: %s@." reason;
      res


let () =
  let[@warning "-8"] target_pure [t;i] =
    `App ("=", [
      i;
      `App ("-", [
        `App ("-", [
          `App ("TLC.LibList.length", [`Var "l"]);
          `App ("TLC.LibList.length", [t])
        ]);
        `Int 2
      ])
    ]) in
  let[@warning "-8"] target_expr [t;i] = [|
    `App ("TLC.LibList.app", [
      `App ("TLC.LibList.make", [
        `App ("+", [i; `Int 1]);
        `Var "init"
      ]);
      `App ("TLC.LibList.rev", [
        `Constructor ("::", [
          `Var "init";
          t
        ])
      ])
    ])
  |] in

  let _t = embed Proof_validator.Helper.data in
  match _t (target_pure, target_expr) with
  | None -> print_endline "failed (timeout)"
  | Some false -> print_endline "failed (could not prove)"
  | Some true -> print_endline "success"
