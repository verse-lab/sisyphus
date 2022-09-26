open Containers

module T = Testing_utils.Make (struct let name = "make_rev_list" end)



let () = T.add_test "verify_make_rev_list_old can be parsed without error" (fun () ->
  let proof =
    IO.with_in "../../resources/make_rev_list/Verify_make_rev_list_old.v"
      IO.read_all in
  
  let ctx = Coq.Proof.make [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../resources/make_rev_list" |> Result.get_exn) "ProofsMakeRevList"
  ] in
  let _ = Proof_parser.Parser.parse ctx proof in
 
  Alcotest.(check unit) "program can be without exception" () ()
)


let () = T.run ()
