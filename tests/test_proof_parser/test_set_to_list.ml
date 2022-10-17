open Containers

module T = Testing_utils.Make (struct let name = "set_to_list" end)



let () = T.add_test "verify_set_to_list_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/set_to_list/Verify_set_to_list_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/set_to_list" |> Result.get_exn) "ProofsSetToList";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
