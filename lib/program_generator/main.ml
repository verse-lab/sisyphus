[@@@warning "-33"]

let () =
  let module Ctx = (val Coq.Context.make [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_ok) "Proofs"
  ]) in

  print_endline "hello world!"
