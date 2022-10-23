open Containers

let env =
  let tA = Lang.Type.Var "A" in
  Lang.Type.(function
      | "++" -> [[List tA; List tA], List tA]
      | "make" ->  [[Int; tA], List tA];
      | "length" -> [[List tA], Int]
      | "drop" -> [[Int; List tA], List tA]
      | "-" -> [[Int; Int], Int]
      | "+" -> [[Int; Int], Int]
      | "is_some" -> [[Bool], Bool]
      | _ -> []
    )


let kirans_ctx =
  let open Lang.Type in
  Expr_generator.make_raw_ctx
    ~consts:[Int, [`Int (2); `Int (1); `Var ("arg0"); `Int (0)];
             Bool, [`Var ("arg1")];
             Func  (Some ([Int; (Var "A")],
                          (ADT ( "option", [(Var "B")], None))))
           , [`Var ("f")];

             (List (Var "A")), [`Var ("l")]]
    ~pats:[]
    ~funcs:
      [Int
      , [("+",
          [Int;
           Int]);
         ("-",
          [Int;
           Int]);
         ("length",
          [(List
              (
                Var
                  "A"))
          ]);
         ("length",
          [(List
              (
                Var
                  "B"))
          ])
        ]; Bool
         , [("not", [Bool]);
            ("is_some", [ADT (
                 "option",
                 [(Var "A")],
                 None)]);
            ("is_some", [ADT (
                "option",
                [(Var "B")],
                None)])];
       (List
          (Var "A"))
     , [("take",
         [Int;
          (List
             (
               Var
                 "A"))
         ])
       ];
       (List
          (Var "B"))
     , [("take",
         [Int;
          (List
             (
               Var
                 "B"))
         ])
       ];
       (ADT (
           "option",
           [(Var "A")],
           None))
     , [("list_find_mapi",
         [(Func
             (Some (
                 [Int;
                  (Var
                     "A")],
                 (ADT (
                     "option",
                     [(Var
                         "A")],
                     None)))));
          (List
             (
               Var
                 "A"))
         ]);
        ("list_find_mapi",
         [(Func
             (Some (
                 [Int;
                  (Var
                     "B")],
                 (
                   ADT (
                     "option",
                     [(Var
                         "A")],
                     None)))));
          (List
             (Var
                "B"))
         ])
       ];
       (ADT (
           "option",
           [(Var "B")],
           None))
     , [("list_find_mapi",
         [(Func
             (Some (
                 [Int;
                  (Var
                     "A")],
                 (ADT (
                     "option",
                     [(Var
                         "B")],
                     None)))));
          (List
             (
               Var
                 "A"))
         ]);
        ("list_find_mapi",
         [(Func
             (Some (
                 [Int;
                  (Var
                     "B")],
                 (
                   ADT (
                     "option",
                     [(Var
                         "B")],
                     None)))));
          (List
             (Var
                "B"))
         ])
       ]]

let test_gen_heap () =
  let open Lang.Type in
  let open Expr_generator.Types in

  let fuel = 2 in
  let option_b = ADT ("option", [(Var "B")], None) in

  let exps = Expr_generator.generate_expression kirans_ctx ~fuel ~initial:false option_b in
  let exps = Seq.to_list exps in

  print_endline "Results for Heap Assertion";
  print_endline @@ string_of_int @@ List.length exps;

  List.iter (Format.printf "%a@." Lang.Expr.pp) exps;

  (* list_find_mapi f (take arg0 l) *)
  let expr_ls: Lang.Expr.t = `App ("list_find_mapi", [
      `Var "f"
    ; `App ("take", [
          `Var "arg0" ; `Var "l"
        ])
    ]) in

  assert (List.exists (fun x -> Lang.Expr.equal expr_ls x) exps);
  ()

let () =
  let open Lang.Type in
  let open Expr_generator.Types in
  test_gen_heap ();

  let fuel = 3 in
  let exps = Expr_generator.generate_expression kirans_ctx ~fuel ~blacklisted_vars:["arg1"] ~initial:false Bool in
  let exps = Seq.to_list exps in

  print_endline "Results for Pure Assertion";
  print_endline @@ string_of_int @@ List.length exps;

  List.iter (Format.printf "%a@." Lang.Expr.pp) exps;


  (* let open Lang.Type in *)
  (* let open Expr_generator.Types in *)

  (* let check_generates ~fuel expr_i ty = *)
  (*   let exps = Expr_generator.generate_expression ~initial:false kirans_ctx env ~fuel ty in *)
  (*   assert (List.exists (Lang.Expr.equal expr_i) exps) *)
  (* in *)

  (* check_generates ~fuel:1 (`Int 2) (Int); *)
  (* check_generates ~fuel:1 (`Var "l") (List (Var "A")); *)
  (* check_generates ~fuel:2 (`App ("length", [`Var "l"])) Int; *)
  (* check_generates ~fuel:2 (`App ("length", [`Var "arg0"])) Int; *)
  (* check_generates ~fuel:3 (`App ("-", [ *)
  (*     `App ("length", [`Var "l"]); *)
  (*     `App ("length", [`Var "arg0"]); *)
  (*   ])) Int; *)

  (* let fuel = 3 in *)
  (* let exps = Expr_generator.generate_expression ~initial:false kirans_ctx env ~fuel (Int) in *)

  (* print_endline "Results for Pure Assertion"; *)
  (* print_endline @@ string_of_int @@ List.length exps; *)

  (* let expr_i: Lang.Expr.t = `App ("-", [ *)
  (*     `App ("-", [ *)
  (*         `App ("length", [`Var "l"]); *)
  (*         `App ("length", [`Var "arg0"]); *)
  (*       ]); *)
  (*     `Int 2 *)
  (*   ]) in *)

  (* assert (List.exists (Lang.Expr.equal expr_i) exps); *)
