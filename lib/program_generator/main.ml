[@@@warning "-33"]
open Containers

let old_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_old.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let new_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_new.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let alignment =
  Dynamic.build_alignment
    ~deps:["../../_build/default/resources/seq_to_array/common.ml"]
    ~old_program
    ~new_program ()
  

let () =
  let module Ctx = (val Coq.Context.make [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_exn) "Proofs"
  ]) in

  
  
  print_endline "hello world!"
