Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsArrayFindi Require Import Array_findi_old_ml.

Lemma array_findi_spec :
  forall (A : Type) `{EA : Enc A}
         (a : array A) (f : func) (l : list A) (fp: int -> A -> bool),
    (forall (i: int)(a: A), 0 <= i < length l ->
        SPEC_PURE (f i a)
         POST (fun (b: bool) => \[b = fp i a])) ->
  SPEC (findi a f)
  PRE (a ~> Array l)
  POST (fun (b : option (int * A)) =>
          \[b = list_findi fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec (int * A) 0 (length l) tmp
          (fun (i: int) (b: option (int * A)) =>
             \[b = list_findi fp (take i l)] \*
               a ~> Array l)
       ). { sis_generic_solver. }
  { sis_generic_solver.  }
  { sis_generic_solver. }
  intros res i_b Hres Hexists.
  xvals*. {
    case res as [[i_nd i_vl]|];
      sis_generic_solver.
  }
Qed.
