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
  xref a_t.
  xref a_f.
  xletopaque tmp Htmp.
  xapp (array_iter_spec tmp a l (fun (ls: list A) =>
                                   a_t ~~> filter pp (rev ls) \*
                                   a_f ~~> filter_not pp (rev ls)
       )). {
    sis_solve_start; autorewrite with rew_list filter_lemmas; sis_handle_if.
  }
  xmatch.
  xapp.
  xlet.
  xapp.
  xlet.
  xapp. intros Ht.
  xapp. intros Hf.
  xvals*. { rewrite Pleft_l; autorewrite with rew_list filter_lemmas; auto. }
  { rewrite Pright_l; autorewrite with rew_list filter_lemmas; auto. }
Qed.
