[@@@warning "-33-26"]
open Containers

let old_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_old.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let old_proof =
  let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all in
  fun ctx -> Proof_parser.Parser.parse ctx proof_str

  


let new_program =
  IO.with_in "../../_build/default/resources/seq_to_array/seq_to_array_new.ml" IO.read_all
  |> Lang.Sanitizer.parse_str

let prelude = {coq|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.
|coq}

let spec = {|
Lemma to_array_spec : forall (A: Type) `{EA:Enc A} (l:list A) (s:func) (v: loc),
    SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun (a: loc) => a ~> Array l).
Proof using.
|}


let () =
  let compilation_env = Dynamic.CompilationContext.init () in
  (* build alignment between programs *)
  let alignment =
    Dynamic.build_alignment ~compilation_env
      ~deps:["../../_build/default/resources/seq_to_array/common.ml"]
      ~old_program
      ~new_program () in
  (* build concrete values as well *)
  let concrete =
    Dynamic.build_concrete_trace ~compilation_env
      ~deps:["../../_build/default/resources/seq_to_array/common.ml"]
      new_program in

  (* initialise coq ctx *)
  let ctx = (Coq.Proof.make ~verbose:false [
    Coq.Coqlib.make ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array/" |> Result.get_exn) "Proofs"
  ]) in
  let old_proof = old_proof ctx in
  let ctx =
    Proof_generator.Proof_context.init
      ~compilation_context:compilation_env ~old_proof ~prelude
      ~spec ~alignment ~concrete ~ctx in

  print_endline @@ Proof_generator.Generator.generate ~logical_mappings:[("s", "l")] ctx new_program


