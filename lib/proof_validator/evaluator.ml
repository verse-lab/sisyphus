open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Evaluates expressions to Z3 terms" "valid.eval"))

module StringMap = Map.Make(String)

type ctx = {
  ctx: Z3.context;
  solver: Z3.Solver.solver;
  int_sort: Z3.Sort.sort;
  unit_sort: Z3.Sort.sort;
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

(** [typeof env expr] returns the type of [expr] under the typing
    environment [env] or None.  *)
let rec typeof env (expr: Lang.Expr.t) : Lang.Type.t option =
  (match expr with
   | `Tuple elts ->
     List.all_some (List.map (typeof env) elts)
     |> Option.map (fun tys -> Lang.Type.Product tys)
   | `Var v -> StringMap.find_opt v env.types

   | `Lambda _ -> None
   | `Int _ -> Some Lang.Type.Int
   | `App ("-", _) -> Some Lang.Type.Int
   | `App ("+", _) -> Some Lang.Type.Int
   | `Constructor ("()", []) -> Some Lang.Type.Unit
   | `Constructor ("[]", []) -> None
   | `Constructor ("::", [h; t]) ->
     Option.choice [
       typeof env h |> Option.map (fun ty -> Lang.Type.List ty);
       typeof env t
     ]
   | `App (_, _) -> None
   | `Constructor _ -> None
  )

(** [eval_type ctx ty] evalautes the type [ty] using the Z3 evaluation
    context [ctx].  *)
let rec eval_type (ctx: ctx) (ty: Lang.Type.t) : Z3.Sort.sort =
  Hashtbl.get_or_add ctx.type_map ~k:ty ~f:(fun ty ->
    match ty with
    | Unit -> ctx.unit_sort
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
      let constructors = [nil; cons] in
      let dt = Z3.Datatype.mk_sort_s ctx.ctx (Format.sprintf "list(%s)" @@ Lang.Type.show ty) constructors in
      dt
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
      Log.warn (fun f -> f "treating type %s as opaque Z3 sort@." (Lang.Type.show ty));
      Z3.Sort.mk_uninterpreted_s ctx.ctx ((Lang.Type.show ty))
  )

let rec eval_expr ?(ty: Lang.Type.t option)
          (ctx: ctx)
          (env: env)
          (expr: Lang.Expr.t) =
  match expr, Option.or_lazy ~else_:(fun () -> typeof env expr) ty with
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
    let ty = Option.or_ ~else_:(Option.or_ ~else_:(typeof env l) (typeof env r)) ty in
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
  | (`App ("&&", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Boolean.mk_and ctx.ctx [l;r]
  | (`App ("||", [l;r]), _) ->
    let l = eval_expr ctx env l in
    let r = eval_expr ctx env r in
    Z3.Boolean.mk_or ctx.ctx [l;r]
  | (`App (("TLC.LibList.length" as fname), [ls]), None) when Option.is_none (typeof env ls) ->
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
        Option.or_lazy ~else_:(fun () -> typeof env vl)
          (Option.bind (typeof env ls) (function (List ty) -> Some ty | _ -> None)) in
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
    | args_tys, [_ptys, fapp] ->
      let arg_ty_map =
        let tbl = Hashtbl.create 10 in
        List.combine args_tys args
        |> List.iter (fun (aty, arg) ->
          Option.iter (fun ty ->
            Hashtbl.add tbl aty ty
          ) (typeof env arg)
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
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env h) ->
    let ty = Lang.Type.List (typeof env h |> Option.get_exn_or "invalid type") in
    let cons = Z3.Z3List.get_cons_decl (Hashtbl.find ctx.type_map ty) in
    let h =
      let ty = match ty with Lang.Type.List ty -> Some ty | _ -> None in
      eval_expr ?ty ctx env h in
    let t = eval_expr ~ty ctx env t in
    Z3.Expr.mk_app ctx.ctx cons [h;t]
  | (`Constructor ("::", [h; t]), None) when Option.is_some (typeof env t) ->
    let ty = typeof env t |> Option.get_exn_or "invalid type" in
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
  | (`Constructor ("true", []), _) -> Z3.Boolean.mk_true ctx.ctx
  | (`Constructor ("false", []), _) -> Z3.Boolean.mk_false ctx.ctx
  | (`Lambda _, _)
  | (`Constructor _, _) -> invalid_arg (Format.sprintf "attempt to convert unsupported expression %s to Z3"
                                          (Lang.Expr.show expr))

(** [evaluate_assertion ctx env assn] evaluates the assertion [assn]
   under the evaluation environment [env] and context [ctx].  *)
let evaluate_assertion ctx env = function
  | `Eq (ty, l, r) ->
    let l = eval_expr ~ty ctx env l in
    let r = eval_expr ~ty ctx env r in
    Z3.Boolean.mk_eq ctx.ctx l r
  | `Assert expr ->
    eval_expr ctx env expr

(** [instantiate_property ctx env ~instantiation p] instantiates a
    property [p] using the binding of polymorphic variables given by
    [instantiation] under the evaluation environment [env] and context
    [ctx]. *)
let instantiate_property ctx env ~instantiation (_poly_vars, params, assumptions, concl) =
  let env, params = List.fold_map (fun env (name, ty) ->
    let ty = Lang.Type.subst instantiation ty in
    let sort = eval_type ctx ty in
    let var = Z3.Expr.mk_fresh_const ctx.ctx name sort in
    {types=StringMap.add name ty env.types;
     values=StringMap.add name var env.values}, var
  ) env params in
  let body =
    let assumptions' =
      List.map (function
          `Eq (ty, l, r) ->
          let ty = Lang.Type.subst instantiation ty in
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
  qf

(** [instantiate_property_bound ctx env ~instantiation p] instantiates a
    property [p] using the binding of polymorphic variables given by
    [instantiation] under the evaluation environment [env] and context
    [ctx]. *)
let instantiate_property_bound ctx env ~instantiation (_poly_vars, params, assumptions, concl) =
  let no_vars = ref 0 in
  let fresh () = let v = !no_vars in incr no_vars; v in
  let env, params = List.fold_map (fun env (name, ty) ->
    let ty = Lang.Type.subst instantiation ty in
    let sort = eval_type ctx ty in
    let var = Z3.Quantifier.mk_bound ctx.ctx (fresh ()) sort in
    {types=StringMap.add name ty env.types;
                               values=StringMap.add name var env.values}, (Z3.Symbol.mk_string ctx.ctx name, sort)
  ) env params in
  let body =
    let assumptions' =
      List.map (function
          `Eq (ty, l, r) ->
          let ty = Lang.Type.subst instantiation ty in
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
  qf
