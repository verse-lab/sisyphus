open Containers

module T = Testing_utils.Make (struct let name = "make_rev_list" end)



let () = T.add_test "make_rev_list old parsed without error" (fun () ->
  let prog =
    IO.with_in "../../resources/make_rev_list/make_rev_list_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  Alcotest.(check Testing_utils.program) "program parsed correctly" {
    prelude = [];
    name = "make_rev_list";
    args = [("ls", (List (Var "'a")))];
    body =
      `LetExp (
        (`Var ("r", (Ref (List (Var "'a")))), None,
         `App (("ref", [`Constructor (("[]", []))])),
         `LetLambda (
           ("tmp", `Lambda (
              ([`Var ("x", Var "'a")],
               `Value ( `App ( (":=", [ `Var ("r"); `Constructor ( ("::", [`Var ("x"); `App (("!", [`Var ( "r")]))])) ]))))),
            `LetExp ((`Var ("unused", Unit), None,
                      `App (("List.iter",
                             [`Var ("tmp");
                              `Var ("ls")])),
                      `Value (`App (("!", [`Var ("r")])))))))));
    logical_mappings=[]
  }
    prog
)

let () = T.add_test "make_rev_list new parsed without error" (fun () ->
  let prog =
    IO.with_in "../../resources/make_rev_list/make_rev_list_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  Alcotest.(check Testing_utils.program) "program parsed correctly" {
    prelude = [];
    name = "make_rev_list";
    args = [("ls", (List (Var "'a")))];
    body =
      `LetLambda (
        ("tmp",
         `Lambda (([`Var ("acc", List (Var "'a"));
                    `Var ("x", Var "'a")],
                   `Value (`Constructor ("::", [`Var "x"; `Var "acc"])))),
         `LetExp (
           (`Var ("result", List (Var "'a")), None,
            `App ("List.fold_left", [
              `Var "tmp"; `Constructor ("[]", []); `Var "ls"
            ]), `Value (`Var "result")))));
    logical_mappings=[];
  }
    prog
)



let () = T.run ()
