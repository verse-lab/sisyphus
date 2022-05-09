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
  
let prelude = {coq|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.
|coq}
  

let () =

  let module Ctx = (val Coq.Proof.make [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_exn) "Proofs"
  ]) in
  Ctx.reset ();
  Ctx.add prelude;
  Ctx.exec ();
  
  print_endline "hello world!"
