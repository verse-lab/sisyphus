open Containers

module AH = Ast_helper
module StringMap = Map.Make(String)

let build_test
      ((pure, heap): Dynamic.Concrete.context * Dynamic.Concrete.heap_context)
      (heap_state: (string * [`Ref | `Array ]) list)
      (lambdas: (string * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) list)
      (invariant: (string * string list))
      (body: Parsetree.expression) =
  let let_ var exp body =
    AH.Exp.let_ Nonrecursive [
      AH.Vb.mk
        (AH.Pat.var Location.(mknoloc var))
        exp
    ] body in
  let (let+) x f = x f in
  let rec with_pure_bindings ls kont =
    match ls with
    | (name, exp) :: t ->
      let+ rest = with_pure_bindings t in
      kont (let_ name (Proof_term_evaluator.evaluate_value exp) rest)
    | [] -> with_heap_bindings heap kont
  and with_heap_bindings ls kont =
    match ls with
    | (name, `Array vls)::t ->
      let+ rest = with_heap_bindings t in
      kont
        (let_ name
           (AH.Exp.array (List.map Proof_term_evaluator.evaluate_value vls))
           rest)
    | (name, `PointsTo vl)::t ->
      let+ rest = with_heap_bindings t in
      kont (let_ name
              (AH.Exp.apply (AH.Exp.ident (Location.mknoloc Longident.(Lident "ref")))
                 [Nolabel, (Proof_term_evaluator.evaluate_value vl)])
              rest)
    | [] ->
      with_function_definitions lambdas kont
  and with_function_definitions lambdas kont =
    match lambdas with
    |(name, lam)::t ->
      let+ rest = with_function_definitions t in
      kont (let_ name (Proof_term_evaluator.evaluate_lambda lam)
              rest)
    | [] ->
      fun invariant_body ->
        let (invariant_name, invariant_args) = invariant in
        let lambda =
          List.rev invariant_args
          |> List.fold_left (fun lam arg ->
            AH.Exp.fun_ Nolabel None (AH.Pat.var Location.(mknoloc arg)) lam
          ) (Proof_term_evaluator.evaluate heap_state invariant_body) in
        kont (let_ invariant_name
          lambda
          body) in
  let ast_builder = with_pure_bindings pure in
  fun ctx invariant_body ->
    let+ ast = Fun.flip ast_builder invariant_body in
    let ast =
      AH.Exp.fun_ Nolabel None
        (AH.Pat.construct (Location.mknoloc (Longident.Lident "()")) None) @@
      AH.Exp.apply (AH.Exp.ident Location.(mknoloc Longident.(Lident "ignore"))) [Nolabel, ast] in
    (* print_endline @@ Format.to_string Pprintast.expression ast; *)
                       
    let body : unit -> unit = Dynamic.CompilationContext.eval ctx ast in
    try
      body (); true
    with
    | Assert_failure (_, _, _) -> false
    | e ->
      Format.printf "evaluation of invariant failed dynamic tests with exception %s@." (Printexc.to_string e);
      false
