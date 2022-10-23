module T = Testing_utils.Make (struct let name = "array_findi" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      (Var "A"), [`App (("TLC.LibContainer.read", [`Var ("l"); `Int (0)])) ];
      Int, [`Var ("arg0"); `Int (0); `Int (1); `Int (2)];
      Bool, [`Var ("arg1")];
      (List (Var "A")), [`Var ("l")];
      (Func (Some ([Int; (Var "A") ], Bool))), [`Var "f"]
    ]
    ~pats:[]
    ~funcs:Lang.Type.[
      (Var "A"), [("option_value_snd", [(Var "A"); (ADT ("option", [(Product [Int; (Var "A")])], None)) ])];
      Int, [
        ("+", [Int; Int]);
        ("-", [Int; Int]);
        ("length", [(List (Var "A")) ]);
        ("option_value_fst", [Int; (ADT ("option", [(Product [Int; (Var "A")])], None)) ])
      ];
      Bool, [
        ("is_some", [(ADT ("option", [(Var "A")], None)) ]);
        ("is_some", [(ADT ("option", [(Product [Int; (Var "A")])], None)) ] );
        ("not", [Bool])
      ];
      (List (Var "A")), [("take", [Int; (List (Var "A")) ])];
      (ADT ("option", [(Product [Int; (Var "A")])], None)), [
        ("list_findi", [(Func (Some ([Int; (Var "A") ], Bool))); (List (Var "A"))])
      ]]

let pure_ty = Lang.Type.Bool
let pure_expr =
  `App ("not", [
    `App ("is_some", [
      `App ("list_findi", [
        `Var "f";
        `App ("take", [`Var "arg0"; `Var "l"]);
      ])
    ])
  ])

let heap1_ty = Lang.Type.Var "A"
let heap1_expr =
  `App ("option_value_snd", [
    `App ("TLC.LibContainer.read", [`Var "l"; `Int 0]);
    `App ("list_findi", [`Var "f"; `App ("take", [`Var "arg0"; `Var "l"]);])
  ])

let heap2_ty = Lang.Type.Int
let heap2_expr =
  `App ("option_value_fst", [
    `Int 0;
    `App ("list_findi", [`Var "f"; `App ("take", [`Var "arg0"; `Var "l"]);])
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
  T.add_slow_test "generates first heap candidate" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression ~initial:true ctx
        heap1_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap1_expr) pure_candidates
  end

let () =
  T.add_slow_test "generates second heap candidate" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression ~initial:true ctx
        heap2_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap2_expr) pure_candidates
  end

let () = T.run ()
