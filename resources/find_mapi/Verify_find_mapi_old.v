Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Solver.
From Common Require Import Utils.

From ProofsFindMapi Require Import Find_mapi_old_ml.

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
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec B 0 (length l) tmp (fun (i: credits) (res: option B) =>
               a ~> Array l \* \[res = list_find_mapi fp (take i l)]
          )
       ). { sis_generic_solver. } { sis_generic_solver. } { sis_generic_solver. }
  intros res i [Hi Himpl] Heq.
  xvals*. {
    destruct res as [ res_vl|]; simpl in Himpl;
      sis_generic_solver.
  }
Qed.
