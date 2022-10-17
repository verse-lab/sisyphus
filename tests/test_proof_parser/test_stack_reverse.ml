open Containers

module T = Testing_utils.Make (struct let name = "stack_reverse" end)



let () = T.add_test "verify_stack_reverse_old can be parsed without error" (fun () ->
    let proof =
      IO.with_in "../../resources/stack_reverse/Verify_stack_reverse_old.v"
        IO.read_all in

    let ctx = Coq.Proof.make [
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/stack_reverse" |> Result.get_exn) "ProofsStackReverse";
        Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/common" |> Result.get_exn) "Common";
      ] in
    let _ = Proof_parser.Parser.parse ctx proof in

    Alcotest.(check unit) "program can be without exception" () ()
  )


let () = T.run ()
