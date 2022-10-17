open Containers

module T = Testing_utils.Make (struct let name = "seq_to_array" end)



let () = T.add_test "verify_seq_to_array_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/seq_to_array" |> Result.get_exn) "Proofs";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
