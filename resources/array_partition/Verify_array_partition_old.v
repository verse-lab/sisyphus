Set Implicit Arguments.
Generalizable Variable A EA.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_arr.
From Common Require Import Tactics Utils Solver.

From ProofsArrayPartition Require Import Array_partition_old_ml.

Lemma array_partition_spec :
  forall (A : Type) `{EA : Enc A} (p: func) (a: array A)
         (pp : A -> bool) (l: list A),
  (forall a: A,
      SPEC (p a)
      PRE (\[])
      POST (fun (b: bool) => \[b = pp a])
  ) ->
  SPEC (partition p a)
  PRE (a ~> Array l)
  POST (fun '((a_t, a_f) : (loc * loc)) =>
          a ~> Array l \*
          a_t ~> Array (filter pp l) \*
            a_f ~> Array (filter_not pp l)
  ).
Proof using (All).
  xcf.
  xapp.
  xif as Hcond.
  - xapp. intros a_t.
    xapp. intros a_f.
    xvals*. { sis_generic_solver. }
    { sis_generic_solver. }
  - xinhab.
    xapp. { auto. }
    xalloc a_t a_t_data Ha_t_data.
    xapp. { auto. }
    xalloc a_f a_f_data Ha_f_data.
    xref c_t.
    xref c_f.
    xletopaque tmp Htmp.
    xapp (array_iter_spec tmp a (fun (prefix: list A) =>
                                     c_t ~~> (length (filter pp prefix)) \*
                                       c_f ~~> (length (filter_not pp prefix)) \*
                                       a_t ~> Array (
                                         (filter pp prefix) ++ drop (length (filter pp prefix)) a_t_data
                                       ) \*
                                       a_f ~> Array (
                                         (filter_not pp prefix) ++ drop (length (filter_not pp prefix)) a_f_data
                                       )
            )
         ). { sis_generic_solver. }
    xmatch.
    xapp.
    xapp. { sis_generic_solver. }
    intros a_left.
    xapp.
    xapp. { sis_generic_solver. }
    intros a_right.
    xvals*. {
      sis_generic_solver.
    } {
      sis_generic_solver.
    }
Qed.
