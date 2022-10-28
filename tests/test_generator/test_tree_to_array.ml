module T = Testing_utils.Make (struct let name = "tree_to_array" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      (Int, [ `Var "arg1"; `Var "idx"; `Var "len"; `Int 1 ]);
      (List (Var "A"), [ `Var "arg0"; `Var "elts" ]);
      (ADT ("Tree.tree", [ Var "A" ], None), [ `Var "t" ]);
    ]
    ~pats:Lang.Type.[
      (Int, [ `App ("length", [ `PatVar ("arg_0", List (Var "A")) ]) ]);
      (List (Var "A"),
        [ `App ("drop", [`PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A"))]);
          `App ("drop", [`App ("length", [ `PatVar ("arg_0", List (Var "A"))]); `PatVar ("arg_1", List (Var "A"))]);
          `App ("++", [`PatVar ("arg_0", List (Var "A")); `PatVar ("arg_1", List (Var "A"))]);
          `App ("++", [`PatVar ("arg_0", List (Var "A")); `App ("drop", [`PatVar ("arg_0", Int); `PatVar ("arg_1", List (Var "A"));])]);
        ]) ]
    ~funcs:Lang.Type.[
      (Var "A", [
         ("fold_left", [
            Func (Some ([ Var "A"; Var "A" ], Var "A"));
            Var "A";
            List (Var "A");
          ]);
         ("thead", [ ADT ("Tree.tree", [ Var "A" ], None) ]);
       ]);
      (Int, [
         ("+", [ Int; Int ]);
         ("-", [ Int; Int ]);
         ("length", [ List (Var "A") ]);
       ]);
      (List (Var "A"), [
         ("++", [ List (Var "A"); List (Var "A") ]);
         ("drop", [ Int; List (Var "A") ]);
         ("make", [ Int; Var "A" ]);
         ("rev", [ List (Var "A") ]);
         ("tol", [ ADT ("Tree.tree", [ Var "A" ], None) ]);
       ]);
    ]



let pure_ty = Lang.Type.Int
let pure_expr = `App ("-", [ `App ("-", [`Var "len"; `App ("length", [`Var "arg0"])]); `Int 1])

let heap_ty = Lang.Type.(List (Var "A"))
let heap_expr = `App ("++", [ `App ("make", [ `App ("+", [`Var "arg1"; `Int 1]); `App ("thead", [`Var "t"])]);
                              `App ("rev", [`Var "arg0"]) ])

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
