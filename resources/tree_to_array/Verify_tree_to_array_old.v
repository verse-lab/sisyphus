Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.
From Common Require Import Verify_tree.

From ProofsTreeToArray Require Import Tree_to_array_old_ml.

Lemma tree_to_array_spec :
  forall (A : Type) `{EA : Enc A} (lt : ltree A) (t : ltree A),
  SPEC (tree_to_array t)
  PRE \[Tree lt t]
  POST (fun a : loc => a ~> Array (tree_to_list lt)).
Proof using (All).
  xcf.
  xpullpure Ht.
  xapp (size_spec lt). { auto. }
  xapp (head_spec lt). { auto. }
  Set Ltac Debug.
  xalloc arr data Hdata.
  xapp; try (pose proof (lsize_gt0 lt); math); intros arr data Hdata.
  xapp; intros ri.
  xletopaque f Hf.
  xapp (tree_iter_spec f t lt
                       (fun (ls: list A) =>
                          ri ~~> (length ls)
                             \* arr ~> Array (ls ++ drop (length ls) data))
       ). {
    intros. apply Hf.
    xgo*.
    + apply int_index_prove; try math. rewrite <- !length_eq. rew_list.
      rewrite !lsize_eq, !H in *.
      rewrite !Hdata, !length_drop_nonneg; rewrite !length_make; rew_list; math.
    + rew_list; math.
    + rew_list.
      rewrite !lsize_eq, !H,  !Hdata in *.
      erewrite (@update_app_r _ _ 0 t0 (length t0)); auto; try math.
      f_equal.
      rewrite (drop_nth (make (length t0) (lhead lt)) (lhead lt)
              (make (length r) (lhead lt))). {
        rewrite update_zero; do 2 f_equal; math.
      }
      { rew_list; rewrite make_app; eauto; try math; eauto.
      math_rewrite (1 + length r = length r + 1).
      rewrite make_succ_l; try math; auto. }
      { rewrite length_make; math. }
  } { auto. }
  xmatch.
  xvals*. {
    rewrite Hdata.
    rewrite lsize_eq; rewrite <- (length_make (lhead lt)) at 1; try math.
    rewrite drop_at_length; rew_list; auto.
  }
Qed.
