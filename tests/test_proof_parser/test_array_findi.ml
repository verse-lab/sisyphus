open Containers

module T = Testing_utils.Make (struct let name = "array_findi" end)



let () = T.add_test "verify_array_findi_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/array_findi/Verify_array_findi_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/array_findi" |> Result.get_exn) "ProofsArrayFindi";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
