Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old_ml.

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
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
    xseq.
    xapp (iteri_spec f s l
                     (fun ls => arr ~> Array (ls ++ (make (length l - length ls) x)) )
         )    . { admit. } { admit. } { admit. } 
    (* unification point 2 *)
    xvals. { admit. }
Admitted.
