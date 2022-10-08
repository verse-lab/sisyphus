open Containers

module T = Testing_utils.Make (struct let name = "find_mapi" end)



let () = T.add_test "find_mapi old parsed without error" (fun () ->
  let prog =
    IO.with_in "../../resources/find_mapi/find_mapi_old.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  Alcotest.(check Testing_utils.program) "program parsed correctly" {
    prelude = [];
    name = "find_mapi";
    args = [("a", Array (Var "'a")); ("f", Func (Some ([Int; Var "'a"], ADT ("option", [Var "'b"], None))))];
    body =
      `LetExp (((`Var ("len", Int)), None,
                `App ("Array.length", [`Var "a"]),
                `LetLambda (("tmp",
                             `Lambda (([`Var ("i", Int)],
                                       `Value (`App ("f",
                                                     [`Var "i";
                                                      `App ("Array.get", [`Var "a"; `Var "i"])])))),
                             `LetExp ((`Var ("res", Lang.Type.ADT ("option", [Var "'b"], None)),
                                       None,
                                       `App ("until_upto", [`Int 0; `Var "len"; `Var "tmp"]),
                                       `Value (`Var "res")))))));
    logical_mappings=[]
  } prog
)

let () = T.add_test "find_mapi new parsed without error" (fun () ->
  let prog =
    IO.with_in "../../resources/find_mapi/find_mapi_new.ml" IO.read_all
    |> Lang.Sanitizer.parse_str in

  Alcotest.(check Testing_utils.program) "program parsed correctly" {
    prelude = [];
    name = "find_mapi";
    args = [("a", Array (Var "'a")); ("f", Func (Some ([Int; Var "'a"], ADT ("option", [Var "'b"], None))))];
    body = `LetExp (
      (`Var ("len", Int), None,
       `App ("Array.length", [`Var "a"]),
       `IfThenElse (
         (`App (("=", [`Var ("len"); `Int (0)])),
          `Value (`Constructor (("None", []))),
          `LetExp ((`Var ("value_found", Lang.Type.Ref (ADT ("option",[Var "'b"], None))), None,
                    `App ("ref", [`Constructor ("None", [])]),
                    `LetLambda ("tmp",
                                `Lambda (([`Var ("i", Lang.Type.Int)],
                                          `LetExp (
                                            (`Var ("res", Lang.Type.ADT ("option", [Var "'b"], None))),
                                            None, `App ("f", [`Var "i"; `App ("Array.get", [`Var "a"; `Var "i"])]),
                                            `LetExp ( `Var ("found", Lang.Type.Bool), None, `App ("option_is_some",[`Var "res"]),
                                                      `IfThen (
                                                        (`Var ( "found"),
                                                         `Value ( `App ( (":=", [`Var ("value_found"); `Var ( "res")]))),
                                                         `LetExp ( (`Var ("res", Bool), None,
                                                                    `App ("not", [`Var "found"]),
                                                                    `Value ( `Var ( "res")))))))))),
                                `LetExp ( (`Var ("unused", Bool), None,
                                           `App ("while_upto", [`Int 0; `Var "len"; `Var "tmp"]),
                                           `Value ( `App ( ("!", [`Var ( "value_found") ]))))))))))));
    logical_mappings=[];
  }
    prog
)



let () = T.run ()
