module T = Testing_utils.Make (struct let name = "sll_partition" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Int, [`Int 1];
      Func (Some ([Var "A"], Bool)), [`Var "p"];
      List (Var "A"), [`Var "arg0"; `Var "ls"]
    ]
    ~pats:Lang.Type.[
      (List (Var "A"),
            [ `App ("rev", [`PatVar ("arg_0", List (Var "A"))]);
              `App
                ( "filter_not",
                  [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                    `PatVar ("arg_1", List (Var "A")) ] );
              `App
                ( "filter_not",
                  [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                    `App ("rev", [`PatVar ("arg_0", List (Var "A"))]) ] );
              `App
                ( "filter",
                  [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                    `PatVar ("arg_1", List (Var "A")) ] );
              `App
                ( "filter",
                  [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                    `App ("rev", [`PatVar ("arg_0", List (Var "A"))])])])]
    ~funcs:Lang.Type.[
      Int, ["+", [Int; Int]; "-", [Int; Int]];
      (List (Var "A"),
       [ "filter", [Func (Some ([Var "A"], Bool)); List (Var "A")];
         "filter_not", [Func (Some ([Var "A"], Bool)); List (Var "A")];
         "rev", [List (Var "A")]])]

let heap1_ty = Lang.Type.(List (Var "A"))
let heap1_expr = `App ("filter", [ `Var "p"; `App ("rev", [`Var "arg0"])])

let heap2_ty = Lang.Type.(List (Var "A"))
let heap2_expr = `App ("filter_not", [ `Var "p"; `App ("rev", [`Var "arg0"])])


let () =
  T.add_test "generates first heap candidate" begin fun () ->
    let candidates = Expr_generator.generate_expression ~fuel:2 ctx heap1_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap1_expr) candidates
  end

let () =
  T.add_test "generates second heap candidate" begin fun () ->
    let candidates = Expr_generator.generate_expression ~fuel:2 ctx heap2_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap2_expr) candidates
  end

let () = T.run ()
