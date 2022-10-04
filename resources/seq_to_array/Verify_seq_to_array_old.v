Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old_ml.
Lemma to_array_spec :
  forall (A : Type) `{EA : Enc A} (l : list A) (s : func) (v : loc),
  SPEC (to_array s)
  PRE \[LSeq l s]
  POST (fun a : loc => a ~> Array l).
Proof using (All).
  xcf.
  xpullpure HLseq.
  apply LSeq_if in HLseq as Hs.
  xapp Hs.
  intros nxt Hnxt.
  case nxt as [ | x nxt2] eqn: H.
  - xmatch_case_0.
    xvalemptyarr. { admit. }
  - xmatch.
    xapp (length_spec s l); auto.
    (* unification point 1 *)
    xalloc arr data Hdata.
    xletopaque f Hf.
    xapp (iteri_spec f s l
                     (fun (ls: list A) => arr ~> Array (ls ++ drop (length ls) (make (length l) x)))
         ). { admit. } { admit. } { admit. }
    (* unification point 2 *)
    xmatch. xvals. { admit. }
Admitted.
