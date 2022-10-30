Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.
From Common Require Import Verify_list.

From ProofsArrayFoldi Require Import Array_foldi_old_ml.

Lemma array_foldi_spec :
  forall (A : Type) `{EA : Enc A} (B : Type) `{EB: Enc B}
         (a : array A) (init: B) (f : func)
         (l : list A)            (fp: int -> A -> B -> B),
    (forall (i: int) (x: A) (acc: B), 0 <= i < length l ->
        SPEC_PURE (f i x acc)
         POST (fun (acc': B) => \[acc' = fp i x acc])) ->
  SPEC (foldi a init f)
  PRE (a ~> Array l)
  POST (fun (b : B) =>
          \[b = list_foldi l init fp] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (nat_fold_up_spec B  0 (length l) tmp init
          (fun (i: int) (res: B) =>
             \[res = list_foldi (take i l) init fp] \*
               a ~> Array l)
       ). { sis_generic_solver. }
  { sis_generic_solver. }
  { sis_generic_solver. }
  xvals*. { sis_generic_solver. }
Qed.

