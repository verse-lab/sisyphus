Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_vec Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsVecFilter Require Import Vec_filter_new_ml.


Lemma vec_filter_spec (A: Type) `{EA: Enc A}:
  forall (f: func) (v: vector A)
         (l: list A) (f_p: A -> bool),
    (forall (x: A),
        SPEC_PURE (f x)
         POST \[= f_p x]
    ) ->
    SPEC (vec_filter f v)
    PRE (v ~> Vector l)
    POSTUNIT (v ~> Vector (filter f_p l)).
Proof.
  xcf.
  xref j.
  xapp (@vec_size_spec A EA).
  xletopaque tmp Htmp.
  xapp (for_upto_spec 0 (length l) tmp
          (fun (i: int) =>
             j ~~> length (filter f_p (take i l)) \*
               v ~> Vector ((filter f_p (take i l)) ++ drop (length (filter f_p (take i l))) l)
       )). {
    intros i Hi; apply Htmp; clear Htmp.
    xinhab.
    xapp. { sis_handle_int_index_prove.
      rewrite length_drop_nonneg; try (rew_list; math).
      split; try math; pose proof (length_filter_take_leq f_p l i);
        pose proof (length_filter l f_p);
        math.
    }

    xapp.
    pose proof (length_filter_take_leq f_p l i);
      pose proof (length_filter l f_p);
      pose proof (length_filter (take i l) f_p).
    rewrite length_take_nonneg in H2; try math.
    rewrite read_app; try math.
    rewrite If_r;  try math.
    rewrite read_drop; try (rew_list; math);
        try (apply int_index_prove; try math; try (rewrite HD; rew_list; math)).
    math_rewrite (length (filter (fun x0 : A => f_p x0) (take i l)) +
                    (i - length (filter (fun x0 : A => f_p x0) (take i l))) = i).

    xif;=> Hfp. (* note: introduces a unit call in the post-condition *)
    - xapp.
      xapp (@vec_set_spec A EA).  {
        sis_handle_int_index_prove.
        rewrite length_drop_nonneg; try (rew_list; math).
      }
      xmatch.
      xapp.
      xapp.
      xval.
      xvals*. {
        rewrite (take_pos_last IA (i + 1)); math_rewrite (i + 1 - 1 = i);
          try sis_handle_int_index_prove; rewrite filter_last, If_l; rew_list; auto; math.
      } {
        sis_handle_list_update.
        rewrite (take_pos_last IA (i + 1)); math_rewrite (i + 1 - 1 = i);
          try sis_handle_int_index_prove; rewrite filter_last, If_l; rew_list; auto.
        f_equal.
        rewrite drop_write_zero; auto; try math.
        do 2 f_equal; math.
      }
    - xval. xvals*. {
        rewrite (take_pos_last IA (i + 1)); math_rewrite (i + 1 - 1 = i);
          try sis_handle_int_index_prove; rewrite filter_last, If_r; rew_list; auto; math.
      } {
        rewrite (take_pos_last IA (i + 1)); math_rewrite (i + 1 - 1 = i);
          try sis_handle_int_index_prove; rewrite filter_last, If_r; rew_list; auto.
        do 2 f_equal; math.
      }
  } { math. }
  xmatch.
  xapp.
  rewrite !take_full_length.
  xif;=> cond.
  - xapp.
    xval.
    xif;=> cond2.
    + xapp (@vec_get_spec A EA). { sis_handle_int_index_prove. }
      xapp.
      xapp.
      xapp (@vec_fill_spec A EA). { eauto. } {
        instantiate (1:=drop (length (filter (fun x : A => f_p x) l)) l).
        rewrite length_drop_nonneg; math.
      } { instantiate (1 := nil); rew_list; auto. }
      xmatch.
      xval.
      xapp.
      xapp. { auto. }
      xmatch.
      xvals*.
    + xval.
      xapp.
      xapp. { auto. }
      xmatch.
      xvals*.
  - xval.
    xif; intros Hv; try (contradiction Hv; auto; math).
    xval.
    xapp.
    xapp (@vec_set_size_spec). { auto. }
    xmatch.
    xvals*.
    Unshelve.  xinhab; auto.
Qed.
