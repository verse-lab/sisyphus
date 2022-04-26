open Containers

let () =
  print_endline "initial: hello world";
  let module Ctx =
   Proof_validator.Proof.Make(struct
      let verbose = false
      let libs = [
        Proof_validator.Coqlib.make
          ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array" |> Result.get_exn)
          "Proofs"
      ]
    end) in

  Ctx.add "Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old_ml.
";
  Ctx.add "Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpullpure HLseq.
  apply LSeq_if in HLseq as Hs.
  assert (1 = 1). { 
";
  Ctx.exec ();
  print_endline (Ctx.debug_current_goal ());
  print_endline "final: hello world"
