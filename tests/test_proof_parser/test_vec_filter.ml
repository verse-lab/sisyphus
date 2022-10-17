open Containers

module T = Testing_utils.Make (struct let name = "vec_filter" end)



let () = T.add_test "verify_vec_filter_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/vec_filter/Verify_vec_filter_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/vec_filter" |> Result.get_exn) "ProofsVecFilter";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
