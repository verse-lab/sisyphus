[@@@warning "-26"]
open Containers

module AH = Ast_helper
module StringMap = Map.Make(String)

let test_invariant heap_spec (pure, heap) ctx =
  assert (Sisyphus_tracing.Wrap.unwrap (Proof_term_evaluator.eval ctx pure) : bool);
  List.iter
    Proof_spec.Heap.Heaplet.(function
      | (v, `Array _), heap_expr ->
        let expr = `App ("=", [ `App ("Array.to_list", [`Var v]); heap_expr ]) in
        assert (Sisyphus_tracing.Wrap.unwrap (Proof_term_evaluator.eval ctx expr) : bool);          
      | (v, `PointsTo _), heap_expr ->
        let expr = `App ("=", [ `App ("!", [`Var v]); heap_expr ]) in
        assert (Sisyphus_tracing.Wrap.unwrap (Proof_term_evaluator.eval ctx expr) : bool);          
      | _ -> ()
    ) (List.combine_shortest heap_spec heap)

let build_test
      ((pure, heap): Dynamic.Concrete.context * Dynamic.Concrete.heap_context)
      (lambdas:
         (string *
          [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) list)
      (invariant: (string * string list))
      (body: Parsetree.expression) =
  let pconst_str str = Parsetree.Pconst_string (str, Location.none, None) in
  let disable_warning no =
    let txt = Format.sprintf "-%d" no in
    let const = AH.Exp.(constant (pconst_str txt)) in
    AH.Attr.mk (Location.mknoloc "warning")
      (PStr [ AH.Str.eval const]) in
  let let_ var exp body =
    AH.Exp.let_ Nonrecursive [
      AH.Vb.mk
        (AH.Pat.var Location.(mknoloc var))
        exp
    ] body in

  let build_binding_function args =
    let wrap arg =
      AH.Exp.apply
        AH.Exp.(ident @@ Location.mknoloc @@
                Longident.(Ldot (Ldot (Lident "Sisyphus_tracing","Wrap"), "wrap")))
        [Nolabel, arg] in
    let build_case name =
      AH.Exp.case
        AH.Pat.(constant (pconst_str name)) @@
      wrap @@ AH.Exp.(ident @@ Location.mknoloc @@ Longident.(Lident name)) in
    AH.Exp.function_ ~attrs:[disable_warning 8; disable_warning 11] begin
      List.map Fun.(build_case % fst) pure @
      List.map Fun.(build_case % fst) heap @
      List.map build_case args
    end in
  let (let+) x f = x f in
  let rec with_pure_bindings ls kont =
    match ls with
    | (name, exp) :: t ->
      let+ rest = with_pure_bindings t in
      kont (let_ name (Proof_term_embedding.embed_value exp) rest)
    | [] -> with_heap_bindings heap kont
  and with_heap_bindings ls kont =
    match ls with
    | (name, `Array vls)::t ->
      let+ rest = with_heap_bindings t in
      kont
        (let_ name
           (AH.Exp.array (List.map Proof_term_embedding.embed_value vls))
           rest)
    | (name, `PointsTo vl)::t ->
      let+ rest = with_heap_bindings t in
      kont (let_ name
              (AH.Exp.apply (AH.Exp.ident (Location.mknoloc Longident.(Lident "ref")))
                 [Nolabel, (Proof_term_embedding.embed_value vl)])
              rest)
    | [] ->
      with_function_definitions lambdas kont
  and with_function_definitions lambdas kont =
    match lambdas with
    |(name, lam)::t ->
      let+ rest = with_function_definitions t in
      kont (let_ name (Proof_term_embedding.embed_lambda lam)
              rest)
    | [] ->
      let (invariant_name, invariant_args) = invariant in
      let app_invariant =
        AH.Exp.apply
          AH.Exp.(ident Location.(mknoloc (Longident.Lident invariant_name)))
          [Nolabel, (build_binding_function invariant_args)] in
      let lambda =
        List.rev invariant_args
            |> List.fold_left (fun lam arg ->
              AH.Exp.fun_ Nolabel None (AH.Pat.var Location.(mknoloc arg)) lam
            ) app_invariant in
      kont (let_ invariant_name lambda body) in
  let ast_builder = with_pure_bindings pure in
  fun ctx ->
    let+ ast = ast_builder in
    let ast =
      AH.Exp.fun_ Nolabel None
        (AH.Pat.var (Location.mknoloc (fst invariant))) @@
      AH.Exp.apply (AH.Exp.ident Location.(mknoloc Longident.(Lident "ignore")))
        [Nolabel, ast] in
    Format.printf "generated test_fun was %a@." Pprintast.expression ast;
    let body : ((string -> Sisyphus_tracing.Wrap.t) -> unit) -> unit =
      Dynamic.CompilationContext.eval ctx ast in
    fun inv ->
      try
        body (test_invariant heap inv); true
      with
      | Assert_failure (_, _, _) -> false
      | e ->
        Format.printf "evaluation of invariant failed dynamic tests \
                       with exception %s@." (Printexc.to_string e);
        false
