module T = Testing_utils.Make (struct let name = "array_of_rev_list" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Var "A", [`Var "x"]; Int, [`Int 0; `Int 1; `Int 2; `Var "len"];
      List (Var "A"), [`Var "_unused"; `Var "arg0"; `Var "l"]]
    ~pats:Lang.Type.[
      (Int,
       [ `App ("-", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)]);
         `App ( "-", [ `PatVar ("arg_0", Int); `App ("+", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)])]);
         `App ("+", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)]) ]);
      (List (Var "A"),
       [`App ("take", [`PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A"))] );
        `App ("take", [ `App ("-", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)]); `PatVar ("arg_1", List (Var "A")) ]);
        `App ("take", [ `App ("+", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)]); `PatVar ("arg_1", List (Var "A")) ]);
        `App ("rev", [`PatVar ("arg_0", List (Var "A"))]);
        `App ("rev", [ `App ( "take", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ] ) ]);
        `App ("drop", [`PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A"))] );
        `App ("drop", [ `App ("-", [`PatVar ("arg_0", Int); `PatVar ("arg_1", Int)]); `PatVar ("arg_1", List (Var "A")) ]);
        `App ("++", [ `PatVar ("arg_0", List (Var "A")); `PatVar ("arg_1", List (Var "A")) ]);
        `App ("++", [ `PatVar ("arg_0", List (Var "A")); `App ("rev", [`PatVar ("arg_0", List (Var "A"))]) ]);
        `App ("++", [ `App ( "take", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ]); `PatVar ("arg_1", List (Var "A")) ] );
        `App ("++", [ `App ( "take", [ `PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A")) ]); `App ("rev", [`PatVar ("arg_0", List (Var "A"))]) ] ) ] )]
    ~funcs:Lang.Type.[
      Int, ["+", [Int; Int]; "-", [Int; Int]; "length", [List (Var "A")]];
      (List (Var "A"), [ "++", [List (Var "A"); List (Var "A")];
                         "drop", [Int; List (Var "A")]; "make", [Int; Var "A"];
                         "rev", [List (Var "A")]; "take", [Int; List (Var "A")]])] 


let heap_ty = Lang.Type.(List (Var "A"))
let heap_expr =
  `App ("++", [
    `App ("make", [ `App ("-", [`Var "len"; `App ("length", [`Var "arg0"])]); `Var "x" ]);
    `App ("++", [`App ("rev", [`Var "arg0"]); `Constructor ("[]", [])]);
  ])

let () =
  T.add_slow_test "generates heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    List.exists (Lang.Expr.equal heap_expr) heap_candidates
  end

let () = T.run ()
