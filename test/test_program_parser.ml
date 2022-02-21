[@@@warning "-27-26-33"]
open Containers

module T = Testing_utils.Make (struct let name = "program_parser" end);;

let pure_expr = Alcotest.testable Program.Expr.pp Program.Expr.equal_expr;;
let slc = Alcotest.testable Program.Statements.pp_slc Program.Statements.equal_slc;;
let pattern = Alcotest.testable Program.Statements.pp_pattern Program.Statements.equal_pattern;;
let statement = Alcotest.testable Program.Statements.pp Program.Statements.equal;;
let func = Alcotest.testable Program.Statements.pp_func Program.Statements.equal_func;;

let test_extracts_to_pure str expr () =
  Alcotest.check pure_expr "extracted pure expression matches"
    expr
    (Program_parser.convert_pure_expression (Program_parser.raw_parse_expr str)) ;;

let test_extracts_to_slc str expr () =
  Alcotest.(check (list slc)) "extracted expression matches slc of" expr
    (Program_parser.convert_slc (Program_parser.raw_parse_expr str)) ;;

let test_extracts_to str expr () =
  Alcotest.(check func) "extracted declaration matches slc of" expr
    (Program_parser.convert_declaration (List.hd (Program_parser.raw_parse_str str))) ;;


T.add_test "parses ints" @@ test_extracts_to_pure "1" (IntExpr (Int 1));;

T.add_test "parses addition of constants" @@ test_extracts_to_pure "1 + 2" (IntExpr (Add (Int 1, Int 2)));;

T.add_test "parses addition of variables" @@ test_extracts_to_pure "x + y" (IntExpr (Add (IntVar "x", IntVar "y")));;

T.add_test "parses addition of constants and variables" @@ test_extracts_to_pure "x + 1" (IntExpr (Add (IntVar "x", Int 1)));;

T.add_test "parses subtraction of constants" @@ test_extracts_to_pure "1 - 2" (IntExpr (Sub (Int 1, Int 2)));;

T.add_test "parses subtraction of constants and variables" @@ test_extracts_to_pure "1 - x" (IntExpr (Sub (Int 1, IntVar "x")));;

T.add_test "parses list nil" @@ test_extracts_to_pure "[]" (ListExpr Nil);;

T.add_test "parses list cons" @@ test_extracts_to_pure "x :: t" (ListExpr (AppList ("cons", [Var "x"; ListExpr (ListVar "t")])));;

T.add_test "parses bool constants" @@ test_extracts_to_pure "false" (BoolExpr (Bool false));;

T.add_test "parses int lt" @@ test_extracts_to_pure "1 < 2" (BoolExpr (Lt (Int 1, Int 2)));;

T.add_test "parses int lt with variables" @@ test_extracts_to_pure "1 < x" (BoolExpr (Lt (Int 1, IntVar "x")));;

T.add_test "parses int eq" @@ test_extracts_to_pure "1 = 2" (BoolExpr (IntEq (Int 1, Int 2)));;

T.add_test "parses int eq with variables on rhs" @@ test_extracts_to_pure "1 = x" (BoolExpr (IntEq (Int 1, IntVar "x")));;

T.add_test "parses int eq with variables on lhs" @@ test_extracts_to_pure "x = 1" (BoolExpr (IntEq (IntVar "x", Int 1)));;

T.add_test "parses list eq" @@ test_extracts_to_pure "x = []" (BoolExpr (ListEq (ListVar "x", Nil)));;

T.add_test "parses tuple" @@ test_extracts_to_pure "(0, [])" (TupleExpr [IntExpr (Int 0); ListExpr Nil]);;

T.add_test "parses array assignment" @@ test_extracts_to_slc "a.(i) <- x; i - 1" [
  `ArrayAssign ("a", Var "i", Var "x");
  `Expr (IntExpr (Sub (IntVar "i", Int 1)))
];;

T.add_test "parses updated to_array function" @@ test_extracts_to {|
let to_array l =
   let len, ls = fold (fun (i, acc) x -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a
|} ("to_array", [Var "l"],
    Program.[`Fold (((Statements.Tuple [(Statements.Var "len"); (Statements.Var "ls")]),
         (Statements.Tuple [(Statements.Var "i"); (Statements.Var "acc")]),
                     "x", [`Expr (TupleExpr [IntExpr (Add (IntVar "i", Int 1));
                                             ListExpr (AppList ("cons",  [Var "x"; ListExpr (ListVar "acc")]))])],
                     (TupleExpr [IntExpr (Int 0); ListExpr Nil]), (Var "l")));
             `MatchPure (("ls",
               [((Statements.Constructor ("[]", [])), [`EmpArray]);
                 ((Statements.Constructor ("::",
                     [(Statements.Var "init"); (Statements.Var "rest")])),
                  [`AllocArray (("a", Var "len", "init"));
                    `LetPure (("idx", IntExpr (Sub (IntVar "len", Int 2))));
                    `ListFold ((Statements.Wildcard, (Statements.Var "i"),
                                "x",
                                [`ArrayAssign (("a", Var "i", Var "x")); `Expr (IntExpr (Sub (IntVar "i", Int 1)))],
                                Var "idx", Var "rest"));
                    `Expr (Var "a")])
                 ]))
            ])
;;



T.add_test "parses updated to_array function with comments" @@ test_extracts_to {|
let to_array l =
   let len, ls = fold (fun (i, acc) x -> (i + 1, x :: acc)) (0, []) l in
  (* len = length' l *)
  (* ls' = rev ls *)
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a
|} ("to_array", [Var "l"],
    Program.[`Fold (((Statements.Tuple [(Statements.Var "len"); (Statements.Var "ls")]),
         (Statements.Tuple [(Statements.Var "i"); (Statements.Var "acc")]),
                     "x", [`Expr (TupleExpr [IntExpr (Add (IntVar "i", Int 1));
                                             ListExpr (AppList ("cons",  [Var "x"; ListExpr (ListVar "acc")]))])],
                     (TupleExpr [IntExpr (Int 0); ListExpr Nil]), (Var "l")));
             `Comment (" len = length' l "); `Comment (" ls' = rev ls ");
             `MatchPure (("ls",
               [((Statements.Constructor ("[]", [])), [`EmpArray]);
                 ((Statements.Constructor ("::",
                     [(Statements.Var "init"); (Statements.Var "rest")])),
                  [`AllocArray (("a", Var "len", "init"));
                    `LetPure (("idx", IntExpr (Sub (IntVar "len", Int 2))));
                    `ListFold ((Statements.Wildcard, (Statements.Var "i"),
                                "x",
                                [`ArrayAssign (("a", Var "i", Var "x")); `Expr (IntExpr (Sub (IntVar "i", Int 1)))],
                                Var "idx", Var "rest"));
                    `Expr (Var "a")])
                 ]))
            ])
;;



T.add_test "parses original to_array function" @@ test_extracts_to {|
let to_array l =
  match l() with
  | Nil -> [| |]
  | Cons (x, _) ->
    let n = length' l in
    let a = Array.make n x in
    iteri
      (fun i x -> a.(i) <- x)
      l;
    a
|} ("to_array", [Var "l"], Program.[`MatchDeferred (("l",
                  [((Statements.Constructor ("Nil", [])), [`EmpArray]);
                    ((Statements.Constructor ("Cons",
                        [(Statements.Var "x"); Statements.Wildcard])),
                     [`Length (("n", Var "l")); `AllocArray (("a", Var "n", "x"));
                       `Iteri (("i", "x", [`ArrayAssign (("a", Var "i", Var "x"))], Var "l"));
                      `Expr (Var "a")])
                    ])) ]
    )
;;


let () = T.run ()
