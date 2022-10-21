module T = Testing_utils.Make (struct let name = "seq_to_array" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Int, [`Int 0; `Int 1; `Int 2; `Var "arg0"]; Bool, [`Var "arg1"];
      Func (Some ([Int; Var "A"], ADT ("option", [Var "B"], None))), [`Var "f"];
      List (Var "A"), [`Var "l"]]
    ~pats:[]
    ~funcs:Lang.Type.[
      (Int, ["+", [Int; Int]; "-", [Int; Int];
             "length", [List (Var "A")];
             "length", [List (Var "B")] ] );
      (Bool, ["is_some", [ADT ("option", [Var "A"], None)];
              "is_some", [ADT ("option", [Var "B"], None)];
              "not", [Bool] ] );
      (List (Var "A"), ["take", [Int; List (Var "A")]]);
      (List (Var "B"), ["take", [Int; List (Var "B")]]);
      (ADT ("option", [Var "A"], None),
       [("list_find_mapi", [Func (Some ([Int; Var "A"], ADT ("option", [Var "A"], None))); List (Var "A") ]);
        ("list_find_mapi", [Func (Some ([Int; Var "B"], ADT ("option", [Var "A"], None))); List (Var "B")])]);
      (ADT ("option", [Var "B"], None), [
         ("list_find_mapi", [Func (Some ( [Int; Var "A"], ADT ("option", [Var "B"], None) )); List (Var "A") ]);
         ("list_find_mapi", [Func (Some ( [Int; Var "B"], ADT ("option", [Var "B"], None) )); List (Var "B") ])])]


let pure_ty = Lang.Type.Bool
let pure_expr =
  `App ("not", [`App ("is_some", [ `App ("list_find_mapi", [`Var "f"; `App ("take", [`Var "arg0"; `Var "l"])]);]);])


let heap_ty = Lang.Type.(ADT ("option", [Var "B"], None))
let heap_expr = `App ("list_find_mapi", [`Var "f"; `App ("take", [`Var "arg0"; `Var "l"])])

let () =
  T.add_test "generates pure candidate" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression
        ~blacklisted_vars:["arg1"] ~fuel:3 ~initial:false ctx
        pure_ty in
    Alcotest.(check bool) "pure candidate is found" true @@
    List.exists (Lang.Expr.equal pure_expr) pure_candidates
  end


let () =
  T.add_slow_test "generates heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ctx heap_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    List.exists (Lang.Expr.equal heap_expr) heap_candidates
  end

let () = T.run ()
