open Containers

module T = Testing_utils.Make (struct let name = "sll_of_array" end)



let () = T.add_test "verify_sll_of_array_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/sll_of_array/Verify_sll_of_array_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/sll_of_array" |> Result.get_exn) "ProofsSllOfArray";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
