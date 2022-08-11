open Containers

let env =
  let tA = Lang.Type.Var "A" in
  Lang.Type.(function
  | "++" -> Some ([List tA; List tA], List tA)
  | "make" -> Some ([Int; tA], List tA);
  | "length" -> Some ([List tA], Int)
  | "drop" -> Some ([Int; List tA], List tA)
  | "-" -> Some ([Int; Int], Int)
  | "+" -> Some ([Int; Int], Int)
  | _ -> None
    )

let kirans_ctx =
  let open Lang.Type in
  Expr_generator.make_raw_ctx
  ~consts:
    [Var ("A"),[`Var "init"];  (Int, [ `Var "idx"; `Var "len";  `Var "arg1";  `Int 1; `Int 2;]);
     (List (Var "A"), [`Var "arg0"; `Var "rest"; `Var "ls"; `Var "l"])]
   ~pats:
     [Int, [`App (("length", [`PatVar (("arg_0", List (Var "A")))]))];
      List (Var "A"), [
      `App (("make",
                      [`PatVar (("arg_0", Int)); `PatVar (("arg_1", Var "A"))]));
                `App (("make",
                       [`App (("length", [`PatVar (("arg_0", List (Var "A")))]));
                         `PatVar (("arg_1", Var "A"))]));
                `App (("drop",
                       [`PatVar (("arg_0", Int)); `PatVar (
                         ("arg_1", List (Var "A")))]));
                `App (("drop",
                       [`PatVar (("arg_0", Int));
                         `App (("make",
                                [`PatVar (("arg_0", Int));
                                  `PatVar (("arg_1", Var "A"))]))
                         ]));
                `App (("drop",
                       [`App (("length", [`PatVar (("arg_0", List (Var "A")))]));
                         `PatVar (("arg_1", List (Var "A")))]));
                `App (("drop",
                       [`App (("length", [`PatVar (("arg_0", List (Var "A")))]));
                         `App (("make",
                                [`PatVar (("arg_0", Int));
                                  `PatVar (("arg_1", Var "A"))]))
                         ]));
                `App (("++",
                       [`PatVar (("arg_0", List (Var "A")));
                         `PatVar (("arg_1", List (Var "A")))]));
                `App (("++",
                       [`PatVar (("arg_0", List (Var "A")));
                         `App (("drop",
                                [`PatVar (("arg_0", Int));
                                  `PatVar (("arg_1", List (Var "A")))]))
                         ]))
                ]]
           ~funcs:
           [Int, [("length", [List (Var "A")]); ("-", [Int; Int]); ("+", [Int; Int])]; List (Var "A")
            ,
            [("rev", [List (Var "A")]); ("make", [Int; Var "A"]);
                 ("drop", [Int; List (Var "A")]); ("++", [List (Var "A"); List (Var "A")])]]




let test_gen_heap () =
  let open Lang.Type in
  let open Expr_generator.Types in

  let fuel = 2 in
  let exps = Expr_generator.generate_expression kirans_ctx env ~fuel (List (Var "A")) in

  print_endline "Results for Heap Assertion";
  print_endline @@ string_of_int @@ List.length exps;

  let expr_ls: Lang.Expr.t = `App ("++", [
    `App ("make", [
      `App ("+", [`Var "arg1"; `Int 1])
    ; `Var "init"
    ])
  ; `App ("drop", [
      `App ("+", [`Var "arg1"; `Int 1])
    ; `Var "l"
    ])
  ]) in

  assert (List.exists (fun x -> Lang.Expr.equal expr_ls x) exps);
  ()

let () =
  let open Lang.Type in
  let open Expr_generator.Types in

  let check_generates ~fuel expr_i ty =
    let exps = Expr_generator.generate_expression ~initial:false kirans_ctx env ~fuel ty in
    assert (List.exists (Lang.Expr.equal expr_i) exps)
  in

  check_generates ~fuel:1 (`Int 2) (Int);
  check_generates ~fuel:1 (`Var "l") (List (Var "A"));
  check_generates ~fuel:2 (`App ("length", [`Var "l"])) Int;
  check_generates ~fuel:2 (`App ("length", [`Var "arg0"])) Int;
  check_generates ~fuel:3 (`App ("-", [
      `App ("length", [`Var "l"]);
      `App ("length", [`Var "arg0"]);
    ])) Int;

  let fuel = 3 in
  let exps = Expr_generator.generate_expression ~initial:false kirans_ctx env ~fuel (Int) in

  print_endline "Results for Pure Assertion";
  print_endline @@ string_of_int @@ List.length exps;

  let expr_i: Lang.Expr.t = `App ("-", [
      `App ("-", [
          `App ("length", [`Var "l"]);
          `App ("length", [`Var "arg0"]);
        ]);
      `Int 2
    ]) in

  assert (List.exists (Lang.Expr.equal expr_i) exps);
