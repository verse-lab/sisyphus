open Containers
module StringMap = Map.Make(String)
module VerificationCondition = Verification_condition
module Evaluator = Evaluator

type pure_candidate = VerificationCondition.expr list -> Lang.Expr.t
type heap_candidate = VerificationCondition.expr list -> VerificationCondition.expr array

type candidate = pure_candidate * heap_candidate

type validator = candidate -> [ `InvalidPure | `InvalidSpatial | `Valid ]

let base_solver_timeout = 100
let challenging_solver_timeout = 30_000

let split_last =
  let rec loop (acc, last) = function
    | [] -> List.rev acc, last
    | h :: t -> loop (last :: acc, h) t in
  function
  | [] -> None
  | h :: t -> Some (loop ([], h) t)

let set_solver_timeout (ctx: Evaluator.ctx) solver timeout =
  let params = Z3.Params.mk_params ctx.ctx in
  Z3.Params.add_int params (Z3.Symbol.mk_string ctx.ctx "timeout") timeout;
  Z3.Solver.set_parameters solver params

let update_with_binding env name (vl,ty)  =
  Evaluator.{
    values = StringMap.add name vl env.values;
    types = StringMap.add name ty env.types
  }

let check solver x =
  match Z3.Solver.check solver [x] with
    Z3.Solver.UNSATISFIABLE -> Some false
  | SATISFIABLE -> Some true
  | UNKNOWN -> None
let prove (ctx : Evaluator.ctx) solver x = Option.map not @@ check solver (Z3.Boolean.mk_not ctx.ctx x)


let check_verification_condition ctx env solver
      (vc: VerificationCondition.vc)
      (gen_pred, gen_values) =
  set_solver_timeout ctx solver base_solver_timeout;
  (* update the env with params  *)
  let env = vc.qf
            |> List.fold_left (fun env (name, ty) ->
              let sort = Evaluator.eval_type ctx ty in
              update_with_binding env name ((Z3.Expr.mk_fresh_const ctx.ctx name sort), ty)
            ) env in
  (* add assumptions to solver *)
  let assumptions = List.map (Evaluator.evaluate_assertion ctx env) vc.assumptions in
  Z3.Solver.add solver assumptions;
  (* user predicate holds with initial parameters *)
  let user_pre_pred = gen_pred vc.param_values |> Evaluator.eval_expr ctx env in
  Z3.Solver.add solver [user_pre_pred];

  (* 1st. check that implies predicate with post param values *)
  let user_post_pred = gen_pred vc.post_param_values |> Evaluator.eval_expr ctx env in

  match prove ctx solver user_post_pred with
  | (None | Some false) -> `InvalidPure
  | Some true ->
    Z3.Solver.add solver [user_post_pred];
    (* 2nd. check user generated post values (with post param values) are equal to
       user generated pre values symbolically evaluated *)
    let user_post_values = gen_values vc.post_param_values |> Array.to_list in
    let user_preval_values =
      let user_pre_values = gen_values vc.param_values |> Array.to_list in
      List.combine user_pre_values (Array.to_list vc.expr_values)
      |> List.map (fun (expr, f) -> f expr) in

    set_solver_timeout ctx solver challenging_solver_timeout;
    List.combine user_post_values user_preval_values
    |> List.map (fun (l,r) ->
      Z3.Boolean.mk_eq ctx.ctx (Evaluator.eval_expr ctx env l) (Evaluator.eval_expr ctx env r)
    ) |> List.fold_left (fun acc goal ->
      match acc with
      | (`InvalidPure | `InvalidSpatial as s) -> s
      | acc ->
        match prove ctx solver goal with
        | (None | Some false) -> `InvalidSpatial
        | Some true -> acc
    ) `Valid


let preload_update_axioms (ctx: Evaluator.ctx) poly_vars =
  List.iter (fun (name, _sort) ->
    let fdecl =
      Z3.FuncDecl.mk_fresh_func_decl ctx.ctx
        (Format.sprintf "TLC.LibContainer.update(%s)" name) [
        Evaluator.eval_type ctx (List (Var name));
        Evaluator.eval_type ctx (Int);
        Evaluator.eval_type ctx (Var name)
      ]  (Evaluator.eval_type ctx (List (Var name)) ) in
    Hashtbl.add ctx.update_map (Var name) fdecl
  ) poly_vars

let declare_function (ctx: Evaluator.ctx) poly_vars (fname, Lang.Type.Forall (vars, sign)) =
  let (let+) x f = List.(>>=) x f in
  let param_tys = split_last sign |> Option.get_exn_or "unexpected func signature" |> fst in
  let bindings =
    let+ vars = List.map_product_l (fun v -> List.map Pair.(make v) poly_vars) vars in
    let fname = fname ^ "(" ^ String.concat "," (List.map snd vars) ^ ")" in
    let poly_binding =
      List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
      |> StringMap.of_list in
    let sign = List.map Lang.Type.(subst poly_binding) sign in
    let fname = Z3.Symbol.mk_string ctx.ctx fname in

    let sign = List.map (Evaluator.eval_type ctx) sign in
    let args, ret = split_last sign |> Option.get_exn_or "empty signature" in
    let fb = Z3.FuncDecl.mk_func_decl ctx.ctx fname args ret in
    [List.map (fun (_, v) -> Lang.Type.Var v) vars, fb] in
  Hashtbl.add ctx.fun_map fname (param_tys, bindings)

let evaluate_property (ctx: Evaluator.ctx) env poly_vars name ((property_poly_vars, _, _, _) as p) =
  List.map_product_l (fun v -> List.map Pair.(make v) poly_vars) property_poly_vars
  |> List.filter_map (fun vars ->
    let instantiation =
      List.map (fun (v, poly_var) -> (v, Lang.Type.Var poly_var)) vars
      |> StringMap.of_list in
    try
      Some (Evaluator.instantiate_property_bound ctx env ~instantiation p)
    with
    | _ ->
      Logs.debug (fun f -> f "failed to add property %s" name);
      None
  )

let build_validator (data: VerificationCondition.verification_condition) =
  let data = VerificationCondition.normalize data in
  let ctx = Z3.mk_context [ ] in
  let solver = Z3.Solver.mk_solver_t ctx (Z3.Tactic.mk_tactic ctx "default") in

  let poly_var_map =
    List.map Fun.(Pair.dup_map @@ Z3.Sort.mk_uninterpreted ctx % Z3.Symbol.mk_string ctx) data.poly_vars
    |> Hashtbl.of_list in
  let int_sort = Z3.Arithmetic.Integer.mk_sort ctx in

  let ctx = Evaluator.{ctx; solver; int_sort; poly_var_map;
                       type_map=Hashtbl.create 10;
                       fun_map=Hashtbl.create 10;
                       update_map=Hashtbl.create 10; } in
  let type_map = StringMap.of_list data.env in

  (* hard code axioms for update function. *)
  preload_update_axioms ctx (Hashtbl.to_list poly_var_map);

  (* declare functions used in verification condition *)
  List.iter (declare_function ctx data.poly_vars) data.functions;

  (* initialise typing env *)
  let env = Evaluator.{values=StringMap.empty; types=type_map} in
  let env =
    {env with values= data.env
                      |> List.rev
                      |> List.to_iter
                      |> Iter.map Pair.(map_snd (Evaluator.eval_type ctx))
                      |> Iter.map Fun.(Pair.dup_map @@ uncurry @@ Z3.Expr.mk_fresh_const ctx.ctx)
                      |> Iter.map Pair.(map_fst fst)
                      |> StringMap.add_iter env.values} in

  (* add initial assumptions *)
  let assumptions =
    List.map (fun (ty, l, r) ->
      let l = Evaluator.eval_expr ~ty ctx env l in
      let r = Evaluator.eval_expr ~ty ctx env r in
      Z3.Boolean.mk_eq ctx.ctx l r
    ) data.assumptions in
  Z3.Solver.add solver assumptions;

  (* add initial properties *)
  List.iter (fun (name, prop) ->
    Z3.Solver.add solver (evaluate_property ctx env data.poly_vars name prop);
  ) begin data.properties end;

  (* once Z3 context initialised, return a generator function that can be used to validate candidate expressions *)
  fun (gen_pred, gen_values) ->
    (* push a new context *)
    Z3.Solver.push solver;

    (* set solver timeout to basic *)
    set_solver_timeout ctx solver base_solver_timeout;

    (* check the initial predicate generated by the user *)
    let user_initial_pred =
      let init_values =
        List.combine (snd data.invariant) (data.initial.param_values)
        |> List.mapi (fun ind (ty, expr) ->
          Format.sprintf "__sisyphyus_var_%d" ind, Evaluator.eval_expr ~ty ctx env expr) in
      let params = List.map (fun (name, _) -> `Var name) init_values in
      let env = {env with values=StringMap.add_list env.values init_values} in
      gen_pred params
      (* |> (fun x -> Format.printf "generated predicate was %a@." Lang.Expr.pp x; x) *)
      |> Evaluator.eval_expr ctx env in

    Format.printf "\ttest 01: checking initial pure@.";
    match prove ctx solver user_initial_pred with
    | (None | Some false) -> Z3.Solver.pop solver 1; `InvalidPure
    | Some true ->
      Format.printf "\t         => PASSED@.";
      Z3.Solver.add solver [user_initial_pred];
      let user_initial_values = gen_values data.initial.param_values |> Array.to_list in
      Format.printf "\ttest 02: checking initial values@.";
      match
        List.combine user_initial_values (Array.to_list data.initial.expr_values)
        |> List.map (fun (l, r) ->
          Z3.Boolean.mk_eq ctx.ctx
            (Evaluator.eval_expr ctx env l)
            (Evaluator.eval_expr ctx env r))
        |> List.fold_left (fun acc pred ->
          match acc with
          | (`InvalidSpatial | `InvalidPure) as acc -> acc
          | acc ->
            match prove ctx solver pred with
            | (None | Some false) -> `InvalidSpatial
            | Some true -> Z3.Solver.add solver [pred]; acc
        ) `Valid
      with
      | (`InvalidSpatial | `InvalidPure) as acc -> Z3.Solver.pop solver 1; acc
      | `Valid ->
        Format.printf "\t         => PASSED@.";
        Format.printf "\ttest 03: checking preserved@.";
        let res =
          List.fold_left (fun acc vc ->
            match acc with
            | (`InvalidSpatial | `InvalidPure) as acc -> acc
            | _ ->
              (* push a new context *)
              Z3.Solver.push solver;
              let res = check_verification_condition ctx env  solver vc (gen_pred, gen_values) in
              Z3.Solver.pop solver 1;
              res
          )  `Valid data.conditions in
        Z3.Solver.pop solver 1;
        begin
          match res with
          | `Valid -> Format.printf "\t         => PASSED@."
          | _ -> Format.printf "\t         => FAILED@.";
        end;
        res
