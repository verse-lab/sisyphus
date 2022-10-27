Set Implicit Arguments.
Generalizable Variables EA.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.
From Common Require Import Verify_tree Verify_list Tree_ml.

From ProofsTreeToArray Require Import Tree_to_array_new_ml.

Lemma tree_to_array_spec :
  forall {A : Type} `{EA : Enc A} (t : tree_ A),
  SPEC (tree_to_array t)
  PRE \[]
  POST (fun a : loc => a ~> Array (tol t)).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (tree_fold_spec tmp (0, nil) t (fun '((i, acc): (int * list (A))) (x: A) => ((i + 1), x :: acc))).
  sep_solve.
  xdestruct len ls Hlenls.
  rewrite list_fold_length_rev in Hlenls.
  injection Hlenls; intros Hls Hlen.
  xalloc arr data Hdata.
  xletopaque idx Hidx.
  xletopaque tmp1 Htmp1.
  xapp (list_fold_spec (tmp1) (idx) (ls)
          (fun (ls: list (A))
               (i: int) =>
             \[ (i = len - length ls - 1) ]
               \* arr ~> Array ((make (i + 1) (thead t)) ++ rev ls))). {
    sis_solve_start; rew_list; auto. 
    + apply int_index_prove; try math;
        rewrite <- ?length_eq, H, Hlen, <- (length_rev (tol t)), <- Hls, Heq;
        rew_list; try math;
        rewrite ?length_make; rew_list; math.
    + math.
    + assert (acc >= 0). {
        rewrite H, Hlen, <- (length_rev (tol t)), <- Hls, Heq; rew_list; math.
      }
      rewrite update_app_l; rewrite ?length_make; try math.
      rewrite make_succ_r; try math.
      erewrite (@update_app_r _ _ 0); eauto; rewrite ?length_make; try math.
      rewrite update_zero; rew_list; auto.
      do 2 f_equal; math.
      }
      { rew_list; math. } { rewrite Hidx, Hdata; rew_list; f_equal; math. } 
  intros unused Hunused.
  xmatch.
  xvals. {
    rewrite Hunused, Hlen, Hls, length_rev.
    math_rewrite ((length (tol t) - length (tol t) - 1 + 1) = 0);
    rewrite make_zero, rev_rev; rew_list; auto.
  }
Qed.
