Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.
From Common Require Import Verify_opt.

From Common Require Import Tactics Utils Solver.

From ProofsFindMapi Require Import Find_mapi_new_ml.


Lemma find_mapi_spec :
  forall (A : Type) `{EA : Enc A}  (B : Type) `{EB : Enc B}
         (a: array A) (f: func) (l: list A) (fp: credits -> A -> option B),
    (forall (i: int) (a: A),
        SPEC_PURE (f i a)
          POST (fun (b: option B) => \[b = fp i a])) ->
  SPEC (find_mapi a f)
  PRE (a ~> Array l)
  POST (fun (b : option B) => \[ b = list_find_mapi fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp Array_proof.length_spec.
  xif as Hcond.
  - xvals*. { sis_generic_solver. }
  - xref value_found.
    xletopaque tmp Htmp.
    xapp (while_upto_spec 0 (length l) tmp (fun (i: credits) (res: bool) =>
               \[res = negb (is_some (list_find_mapi fp (take i l)))] \*
                 a ~> Array l \*
                 value_found ~~> list_find_mapi fp (take i l) 
          )
         ). {
      intros i Hi; apply Htmp; clear Htmp.
      sis_symexec; sis_generic_solver.
  } { sis_generic_solver. } { sis_generic_solver. }
  intros res i [Hi Himpl] Heq.
    xmatch.
    xapp.
    xvals*. {
      destruct res;
        sis_generic_solver.
  }
Qed.

