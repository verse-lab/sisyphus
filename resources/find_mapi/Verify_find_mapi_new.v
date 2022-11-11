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
xapp.
xif as H_cond.
-
xvals.
{
sis_generic_solver.
}
-
xref value_found.
xletopaque tmp Htmp.
xapp (Common.Verify_combinators.while_upto_spec (0) ((TLC.LibListZ.length (l))) (tmp) (fun (i: int) (res: bool) => \[ (res = (negb (is_some ((list_find_mapi (fp) ((take (i) (l)))))))) ]  \* value_found ~~> (list_find_mapi (fp) ((take (i) (l))))
     \* a ~> Array l
     )).
{
  introv Hl. apply Htmp; clear Htmp.
  sis_symexec; sis_generic_solver.
}
{
sis_generic_solver.
}
{
sis_generic_solver.
}
intros unused Hunused.
intros.
try xdestruct.
xapp.
xvals.
{ sis_generic_solver.
  destruct H0 as [Hlen Himpl]; unfold list_find_mapi in *.
  destruct (list_find_mapi_internal 0 fp (take Hunused l)) eqn:Heq.
  - rewrite <- (@list_eq_take_app_drop A Hunused l); try math.
    rewrite find_mapi_app_l; rewrite Heq; sis_generic_solver.
  - sis_normalize_opt_of_bool; simpl in Himpl.
    sis_generic_solver.
}
Qed.
