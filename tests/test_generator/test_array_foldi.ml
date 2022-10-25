module T = Testing_utils.Make (struct let name = "array_foldi" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Var "B", [`Var "init"];
      Int, [`Int 0; `Int 1; `Int 2];
      List (Var "A"), [`Var "arg0"; `Var "l"];
      Func (Some ([Int; Var "A"; Var "B"], Var "B")), [`Var "f"]
    ]
    ~pats:[]
    ~funcs:Lang.Type.[
      (Var "A",
       [("list_foldi", [List (Var "A"); Var "A"; Func (Some ([Int; Var "A"; Var "A"], Var "A"))]);
        ("list_foldi", [List (Var "B"); Var "A"; Func (Some ([Int; Var "B"; Var "A"], Var "A"))])]);
      (Var "B", [("list_foldi", [List (Var "A"); Var "B"; Func (Some ([Int; Var "A"; Var "B"], Var "B"))]);
                 ("list_foldi", [List (Var "B"); Var "B"; Func (Some ([Int; Var "B"; Var "B"], Var "B"))])]);
      (Int, ["+", [Int; Int]; "-", [Int; Int]; "length", [List (Var "A")]; "length", [List (Var "B")] ] );
      List (Var "A"), ["take", [Int; List (Var "A")]];
      List (Var "B"), ["take", [Int; List (Var "B")]]
    ]

let heap_ty = Lang.Type.Var "B"
let heap_expr = `App ("list_foldi", [ `Var "arg0"; `Var "init"; `Var "f" ])


let () =
  T.add_slow_test "generates first heap candidate" begin fun () ->
    let heap_candidates =
      Expr_generator.generate_expression ~fuel:2 ~initial:true ctx
        heap_ty in
    Alcotest.(check bool) "heap candidate is found" true @@
    Containers.Seq.exists (Lang.Expr.equal heap_expr) heap_candidates
  end


let () = T.run ()
