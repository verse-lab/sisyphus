Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsArrayPartition Require Import Array_partition_new_ml.

Lemma array_partition_spec :
  forall (A : Type) `{EA : Enc A} (p: func) (a: array A)
         (pp : A -> bool) (l: list A),
  (forall a: A,
      SPEC (p a)
      PRE (\[])
      POST (fun (b: bool) => \[b = pp a])) ->
  SPEC (partition p a)
  PRE (a ~> Array l)
  POST (fun '((a_t, a_f) : (loc * loc)) =>
          a ~> Array l \*
          a_t ~> Array (filter pp l) \*
            a_f ~> Array (filter_not pp l)
  ).
Proof using (All).
xcf.
xref left_ptr.
xref right_ptr.
xletopaque tmp Htmp.
xapp (Common.Verify_arr.array_iter_spec (tmp) (a) (fun (t: list (A)) =>  right_ptr ~~> ((filter (pp) (nil)) ++ (drop ((1 + ((length (t)) - 1))) ((t ++ (filter_not (pp) ((rev (t)))))))) \* left_ptr ~~> ((filter (pp) (nil)) ++ (drop ((1 + ((length (t)) - 1))) (((t ++ nil) ++ (filter (pp) ((rev (t))))))))

)).
{
  sis_generic_solver; rewrite !drop_app_r; sis_generic_solver.
}
xmatch.
xapp.
xlet.
xapp.
xlet.
xapp.
intro left.
xapp.
intro right.
xvals.
{
  subst; rewrite !drop_app_r; sis_generic_solver.
}
{ subst; rewrite !drop_app_r; sis_generic_solver. }
Qed.
