open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Converts extracted proofs to OCaml programs" "analysis.test"))

module AH = Ast_helper
module StringMap = Map.Make(String)

type enc_fun = Lang.Expr.t -> Proof_spec.Heap.Heaplet.t
let pp_enc_fun fmt vl = Proof_spec.Heap.Heaplet.pp fmt (vl (`Var "??"))

type test_fun = Lang.Expr.t -> Lang.Expr.t
let pp_test_fun fmt vl = Format.fprintf fmt "(fun (??) -> %a)" Lang.Expr.pp (vl (`Var "??"))

let test_invariant (pure, heap) ctx =
  assert (Sisyphus_tracing.Wrap.unwrap (Proof_term_evaluator.eval ctx pure) : bool);
  List.iter
    Proof_spec.Heap.Heaplet.(fun ((_, test_fun), heap_expr) ->
      let test_expr = test_fun heap_expr in
      assert (Sisyphus_tracing.Wrap.unwrap (Proof_term_evaluator.eval ctx test_expr) : bool)
    ) (heap)

let build_test
      ((pure, heap): Dynamic.Concrete.context * Dynamic.Concrete.heap_context)
      (lambdas:
         (string *
          [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) list)
      (hofs: (string * Parsetree.expression) list)
      (heap_spec: Proof_spec.Heap.Heaplet.t list)
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
      List.map Fun.(build_case % fst) hofs @
      List.map build_case args @
      [AH.Exp.case AH.Pat.(var (Location.mknoloc "sisyphus_matching_var")) @@
       AH.Exp.apply
         AH.Exp.(ident @@ Location.mknoloc @@ Longident.Lident "failwith") [
         Nolabel, AH.Exp.apply AH.Exp.(ident @@ Location.mknoloc @@ Longident.Lident "^") [
           Nolabel, AH.Exp.constant (Pconst_string ("use of unknown variable ", Location.none, None));
           Nolabel, AH.Exp.ident @@ Location.mknoloc @@ Longident.Lident "sisyphus_matching_var"
         ]
       ]
      ]
    end in
  let (let+) x f = x f in
  let rec with_pure_bindings ls kont =
    match ls with
    | (name, exp) :: t ->
      let+ rest = with_pure_bindings t in
      kont (let_ name (Proof_term_embedding.embed_value exp) rest)
    | [] -> with_hof_bindings hofs kont
  and with_hof_bindings ls kont =
    match ls with
    | (name, exp) :: t ->
      let+ rest = with_hof_bindings t in
      kont (let_ name exp rest)
    | [] -> with_heap_bindings heap kont
  and with_heap_bindings ls kont =
    match ls with
    | (name, `Array vls)::t ->
      let+ rest = with_heap_bindings t in
      kont
        (let_ name
           (AH.Exp.array (List.map Proof_term_embedding.embed_value vls))
           rest)
    | (name, `PointsTo (`Opaque _ as vl))::t ->
      let+ rest = with_heap_bindings t in
      kont (let_ name (Proof_term_embedding.embed_value vl)
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
    Configuration.dump_output "test-fun" (fun f -> f "%a" Pprintast.expression ast);
    Log.debug (fun f -> f "generated test_fun was %a@." Pprintast.expression ast);
    let body : ((string -> Sisyphus_tracing.Wrap.t) -> unit) -> unit =
      Dynamic.CompilationContext.eval ctx ast in
    fun inv ->
      try
        body (test_invariant inv); true
      with
      | Assert_failure (_, _, _) -> false
      | e ->
        Log.warn (fun f ->
          f "evaluation of invariant %s failed dynamic tests \
             with non-assert exception %s@."
            ([%show: Lang.Expr.t * ((enc_fun * test_fun) * Lang.Expr.t) list] inv)
            (Printexc.to_string e));
        false
