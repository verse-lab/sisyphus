open Containers

module T = Testing_utils.Make (struct let name = "array_of_rev_list" end)



let () = T.add_test "Verify_find_mapi_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/find_mapi/Verify_find_mapi_old.v"
        IO.read_all in

    print_endline proof;
    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/find_mapi" |> Result.get_exn) "ProofsFindMapi";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
