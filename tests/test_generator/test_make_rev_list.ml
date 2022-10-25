module T = Testing_utils.Make (struct let name = "make_rev_list" end)

let ctx = 
  Expr_generator.make_raw_ctx 
    ~consts:Lang.Type.[Int, [`Int (1)];
                       (List (Var "A")), [`Var ("arg0"); `Var ("arg1"); `Var ("ls")]]
    ~pats:Lang.Type.[(List (Var "A")), [`App (("rev", [`PatVar (( "arg_0", (List (Var "A"))))]))]]
    ~funcs:Lang.Type.[Int, [("+", [Int; Int]);
                         ("-", [Int; Int])];
                   (List (Var "A")), [ ("rev", [(List (Var "A"))])]] 


let pure_ty_1 = Lang.Type.(List (Var "A"))
let pure_expr_1 =
  `App ("rev", [ `App ("rev", [ `App ("rev", [ `Var "arg0" ]) ]) ])

let pure_ty_2 = Lang.Type.(List (Var "A"))
let pure_expr_2 =
  `App ("rev", [ `App ("rev", [ `App ("rev", [ `Var "arg1" ]) ]) ])


let () =
  T.add_test "generates pure candidate 1" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression
        ~blacklisted_vars:["arg1"] ~fuel:3 ~initial:false ctx
        pure_ty_1 in
    Alcotest.(check bool) "pure candidate is found" true @@
      Containers.Seq.exists (Lang.Expr.equal pure_expr_1) pure_candidates
  end

let () =
  T.add_test "generates pure candidate 2" begin fun () ->
    let pure_candidates =
      Expr_generator.generate_expression
        ~blacklisted_vars:["arg0"] ~fuel:3 ~initial:false ctx
        pure_ty_2 in
    Alcotest.(check bool) "pure candidate is found" true @@
      Containers.Seq.exists (Lang.Expr.equal pure_expr_2) pure_candidates
  end


let () = T.run ()
