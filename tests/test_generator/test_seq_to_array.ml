module T = Testing_utils.Make (struct let name = "seq_to_array" end)

let ctx = 
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      ((Var "A"), [`Var ("init")]);
      (Int, [`Int (1); `Int (2); `Var ("arg1"); `Var ("idx"); `Var ("len")]);
      (List (Var "A")), [`Var ("arg0"); `Var ("l"); `Var ("ls"); `Var ("rest")]]
    ~pats:Lang.Type.[
      Int, [`App (("length", [`PatVar (("arg_0", Lang.(List (Var "A"))))]))];
      (List (Var "A")), [
        `App (("make", [`PatVar (("arg_0", Int)); `PatVar (( "arg_1", Var "A"))]));
        `App (("make", [`App (("length", [`PatVar (("arg_0", Lang.(List (Var "A"))))]));
                        `PatVar ( ( "arg_1", Var "A"))]));
        `App (("drop", [`PatVar (("arg_0", Int)); `PatVar (("arg_1", Lang.(List (Var "A"))))]));
        `App (("drop", [`PatVar (("arg_0", Int));
                        `App (("make", [`PatVar (("arg_0", Int)); `PatVar (("arg_1", Var "A"))]))]));
        `App (("drop", [`App (("length", [`PatVar (("arg_0", Lang.(List (Var "A"))))]));
                        `PatVar (("arg_1", Lang.(List (Var "A"))))]));
        `App (("drop", [`App (("length", [`PatVar (("arg_0", Lang.(List (Var "A"))))]));
                        `App (("make", [`PatVar (( "arg_0", Int)); `PatVar (("arg_1", Var "A"))]))]));
        `App (("++", [`PatVar (( "arg_0", Lang.(List (Var "A")))); `PatVar (("arg_1", Lang.(List (Var "A"))))]));
        `App (("++", [`PatVar (("arg_0", Lang.(List (Var "A"))));
                      `App (("drop", [`PatVar (("arg_0", Int)); `PatVar (("arg_1", Lang.(List (Var "A"))))])) ]))]]
    ~funcs:Lang.Type.[
      Int, [("+", [Int; Int]);
            ("-", [Int; Int]);
            ("length", [(List (Var "A"))])];
      (List (Var "A")), [("++", [(List (Var "A"));
                                 (List (Var "A"))]);
                         ("drop", [Int; (List (Var "A"))]);
                         ("make", [Int; (Var "A") ]);
                         ("rev", [(List (Var "A"))])]]

let pure_ty = Lang.Type.Int
let pure_expr =
  `App ("-", [
    `App ("+", [ `App ("length", [`Var "rest"]); `App ("length", [`Var "rest"]); ]);
    `App ("+", [ `App ("length", [`Var "ls"]); `App ("length", [`Var "arg0"]); ]);
  ])

let heap_ty = Lang.Type.(List (Var "A"))
let heap_expr =
  `App ("++", [
    `App ("make", [ `App ("-", [`App ("length", [`Var "rest"]); `App ("length", [`Var "arg0"])]); `Var "init" ]);
    `App ("drop", [`App ("length", [`Var "rest"]); `App ("++", [`Var "arg0"; `Var "l"])]);
  ])

let () =
  T.add_test "generates pure candidate" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression
        ~blacklisted_vars:["arg1"] ~fuel:3 ~initial:false ctx
        pure_ty in
    Alcotest.(check bool) "pure candidate is found" true @@
      Containers.Seq.exists (Lang.Expr.equal pure_expr) pure_candidates
  end


let () =
  T.add_slow_test "generates heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
      Containers.Seq.exists (Lang.Expr.equal heap_expr) heap_candidates
  end

let () = T.run ()
