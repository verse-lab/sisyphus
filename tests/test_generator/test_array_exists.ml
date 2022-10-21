module T = Testing_utils.Make (struct let name = "array_exists" end)

let ctx =
  Expr_generator.make_raw_ctx
    ~consts:Lang.Type.[
      Int, [`Int 0; `Int 1; `Int 2; `Var "arg0"];
      Func (Some ([Var "A"], Bool)), [`Var "f"];
      List (Var "A"), [`Var "l"];
      ADT ("option", [Unit], None), [`Var "arg1"] ]
    ~pats:Lang.Type.[ ( Bool,
          [ `App
              ( "existsb",
                [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                  `PatVar ("arg_1", List (Var "A")) ] );
            `App
              ( "existsb",
                [ `PatVar ("arg_0", Func (Some ([Var "A"], Bool)));
                  `App
                    ( "take",
                      [ `PatVar ("arg_0", Int);
                        `PatVar ("arg_1", List (Var "A")) ] ) ] ) ] );
        ( List (Var "A"),
          [ `App
              ( "take",
                [ `PatVar ("arg_0", Int);
                  `PatVar ("arg_1", List (Var "A")) ] ) ] ) ]
    ~funcs:Lang.Type.[
      (Int, ["+", [Int; Int]; "-", [Int; Int];
             "length", [List (Var "A")] ] );
      (Bool, [("existsb", [ Func (Some ([Var "A"], Bool)); List (Var "A") ] );
              "is_some", [ADT ("option", [Var "A"], None)];
              "negb", [Bool]]);
      List (Var "A"), ["take", [Int; List (Var "A")]];
      ADT ("option", [Unit], None), ["opt_of_bool", [Bool]] ]


let pure_ty = Lang.Type.(ADT ("option", [Unit], None))
let pure_expr =
  `App ("opt_of_bool", [`App ("existsb", [`Var "f"; `App ("take", [`Var "arg0"; `Var "l"])])])

let () =
  T.add_test "generates pure candidate" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression
        ~blacklisted_vars:["arg1"] ~fuel:3 ~initial:false ctx
        pure_ty in
    Alcotest.(check bool) "pure candidate is found" true @@
    List.exists (Lang.Expr.equal pure_expr) pure_candidates
  end

let () = T.run ()
