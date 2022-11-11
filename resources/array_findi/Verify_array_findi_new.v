Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.
From Common Require Import Verify_opt.

From ProofsArrayFindi Require Import Array_findi_new_ml.

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
xif as H_cond.
-
xvals.
{
sis_generic_solver.
}
-
xref found.
xref idx.
xinhab.
xapp.
{
sis_generic_solver.
}
xref value.
xletopaque tmp Htmp.
xapp (Common.Verify_combinators.while_upto_spec (0) ((TLC.LibListZ.length (l))) (tmp) (fun (i: int) (res: bool) => \[ (res = (negb (is_some ((list_findi (fp) ((take (i) (l)))))))) ]  \* value ~~> (option_value_snd ((TLC.LibContainer.read (l) (0))) ((list_findi (fp) ((take (i) (l)))))) \* idx ~~> (option_value_fst (0) ((list_findi (fp) ((take (i) (l)))))) \* found ~~> (negb (negb (negb res)))
   \* a ~> Array l
)).
{ sis_generic_solver. }
{
sis_generic_solver.
}
{
sis_generic_solver.
}
intros.
xmatch.
xif as H_cond0.
+
xapp.
xapp.
xvals.
{ unfold list_findi in *.
  destruct (list_findi_internal 0 fp (take x0 l)) as [ | p ] eqn:Heq; sis_generic_solver.
  - rewrite <- (@list_eq_take_app_drop A x0 l); try math; sis_list_deep_solver.
    rewrite findi_app_l; rewrite Heq.
    -- simpl. destruct p; auto.
    -- sis_generic_solver.
  - contradiction Hcond; auto.
}
+
xvals.
{
  destruct x; sis_generic_solver; discriminate Hcond.
}
Qed.
