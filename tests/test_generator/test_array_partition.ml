module T = Testing_utils.Make (struct let name = "array_partition" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Int, [`Int 1];
      Func (Some ([Var "A"], Bool)), [`Var "p"];
      List (Var "A"), [`Var "arg0"; `Var "l"]]
    ~pats:Lang.Type.[
      (Int,
       [ `App ("length", [`PatVar ("arg_0", List (Var "A"))]);
         `App ("length", [`App ("filter_not", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A"))])]);
         `App ("length", [`App ("filter", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A"))])])]);
      (List (Var "A"),
        [`App ("filter_not", [`PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A"))]);
          `App ("filter", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A")) ] );
          `App ("drop", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ] );
          `App ("drop", [ `App ("length", [`PatVar ("arg_0", List (Var "A"))]); `PatVar ("arg_1", List (Var "A")) ] );
          `App ("++", [ `PatVar ("arg_0", List (Var "A")); `PatVar ("arg_1", List (Var "A")) ] );
          `App ("++", [ `PatVar ("arg_0", List (Var "A")); `App ( "drop", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ] ) ] );
          `App ("++", [ `App ( "filter_not", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A")) ] ); `PatVar ("arg_1", List (Var "A")) ] );
          `App ("++", [ `App ( "filter_not", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A")) ] ); `App ("drop", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ] ) ] );
          `App ("++", [ `App ( "filter", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A")) ] ); `PatVar ("arg_1", List (Var "A")) ] );
         `App ("++", [ `App ( "filter", [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool))); `PatVar ("arg_1", List (Var "A")) ] ); `App ("drop", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ] ) ] ) ] )]
    ~funcs:
      Lang.Type.[
        (Int, [ "+", [Int; Int]; "-", [Int; Int]; "length", [List (Var "A")] ] );
        (List (Var "A"), [
           "++", [List (Var "A"); List (Var "A")];
           "drop", [Int; List (Var "A")];
           "filter", [Func (Some ([Var "A"], Bool)); List (Var "A") ];
           "filter_not", [ Func (Some ([Var "A"], Bool)); List (Var "A") ];
           "rev", [List (Var "A")]
         ])]


let heap1_ty = Lang.Type.(List (Var "A"))
let heap1_expr = `App ("filter", [`Var "p"; `App ("rev", [`Var "arg0"])])

let heap2_ty = Lang.Type.(List (Var "A"))
let heap2_expr = `App ("filter_not", [`Var "p"; `App ("rev", [`Var "arg0"])])


let () =
  T.add_test "generates first heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap1_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap1_expr) heap_candidates
  end

let () =
  T.add_test "generates second heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap2_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap2_expr) heap_candidates
  end

let () = T.run ()
