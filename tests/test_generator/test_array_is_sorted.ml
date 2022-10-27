module T = Testing_utils.Make (struct let name = "array_is_sorted" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Int, [`Var ("arg0"); `Int (0);`Int (1)];
      Bool,[`Var ("arg1")];
      (List Int), [`Var ("l")]
    ]
    ~pats:[]
    ~funcs:Lang.Type.[
      Int, [("+", [Int; Int]);
            ("-", [Int; Int]);
            ("length", [(List Int)])];
      Bool, [("is_sorted", [(List Int) ]);
             ("negb", [Bool]);
             ("not", [Bool])];
      (List Int), [("drop", [Int; (List Int)])];
      (ADT ("option", [Unit], None)), [("opt_of_bool", [Bool])]]



let pure_ty = Lang.Type.Bool
let pure_expr = `App ("is_sorted", [`App ("drop", [`Var "arg0"; `Var "l"])])

let heap_ty = Lang.Type.Bool
let heap_expr = `Var "arg1"


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
  T.add_test "generates first heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap_expr) heap_candidates
  end


let () = T.run ()
