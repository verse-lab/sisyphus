Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsSllOfArray Require Import Sll_of_array_old_ml.

Lemma sll_of_array_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (ls: list A),
  SPEC (sll_of_array a)
  PRE (a ~> Array ls)
  POST (fun (s : sll A) => s ~> SLL ls \* a ~> Array ls).
Proof using (All).
  xcf.
  xapp. intros s.
  xapp.
  xletopaque tmp Htmp.
  xapp (for_downto_spec (length ls - 1) 0 tmp
          (fun (i: int) =>
             s ~> SLL ((drop (i + 1) ls)) \*
               a ~> Array ls
       )). { math. } {
    sis_generic_solver.
  } { sis_generic_solver.  }
  xmatch.
  xvals.
Qed.
