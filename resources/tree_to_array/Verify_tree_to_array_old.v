Set Implicit Arguments.
Generalizable Variables EA.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.
From Common Require Import Verify_tree Tree_ml.

From ProofsTreeToArray Require Import Tree_to_array_old_ml.

Lemma tree_to_array_spec :
  forall {A : Type} `{EA : Enc A} (t : tree_ A),
  SPEC (tree_to_array t)
  PRE \[]
  POST (fun a : loc => a ~> Array (tol t)).
Proof using (All).
  xcf.
  xapp+.
  xapp+.
  xalloc arr data Hdata.
  xapp+. intros i.
  xletopaque tmp Htmp.
  xapp (tree_iter_spec tmp t
          (fun (ls: list A) =>
             i ~~> (length ls)
               \* arr ~> Array (ls ++ drop (length ls) data))
       ). {
    sis_solve_start; rew_list; auto. 
    + apply int_index_prove; try math; rewrite <- !length_eq; rew_list.
      rewrite !tree_size_eq in *; rewrite Hdata, Heq, length_drop_nonneg;
        rewrite !length_make; rew_list; try math.
    + math.
    + rewrite !tree_size_eq, !Heq,  !Hdata in *.
      erewrite (@update_app_r _ _ 0 t0 (length t0)); auto; try math.
      f_equal.
      rewrite (drop_nth (make (length t0) (thead t)) (thead t)
              (make (length r) (thead t))). {
        rewrite update_zero; do 2 f_equal; math.
      }
      { rew_list; rewrite make_app; eauto; try math; eauto.
      math_rewrite (1 + length r = length r + 1).
      rewrite make_succ_l; try math; auto. }
      { rewrite length_make; math. }
  }
  xmatch.
  xvals*. {
    rewrite Hdata.
    rewrite tree_size_eq; rewrite <- (length_make (thead t)) at 1; try math.
    rewrite drop_at_length; rew_list; auto.
  }
Qed.
