Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsSllOfArray Require Import Sll_of_array_old_ml.

Lemma sll_of_array_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (ls: list A),
  SPEC (sll_of_array a)
  PRE (a ~> Array ls)
  POST (fun (s : sll A) => s ~> SLL ls \* a ~> Array ls).
Proof using (All).
  xcf.
  xapp (sll_nil_spec).
  intros s.
  xletopaque tmp Htmp.
  xapp (array_iter_spec tmp a ls
          (fun (ls: list A) =>
             s ~> SLL (rev ls)
       )). {
    sis_solve_start.
    xapp (sll_push_spec); xsimpl*.
    rew_list; auto.
  }
  xapp (sll_reverse_spec).
  xval. { xsimpl*; rew_list; auto. }
Qed.
