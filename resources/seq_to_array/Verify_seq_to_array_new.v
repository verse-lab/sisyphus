Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sseq.
From Common Require Import Verify_list.

From Common Require Import Tactics.
From Common Require Import Utils.

From Proofs Require Import Seq_to_array_new_ml.


Lemma to_array_spec :
  forall (A : Type) `{EA : Enc A} (l : list A) (s : func) (v : loc),
  SPEC (to_array s)
  PRE \[LSeq l s]
  POST (fun a : loc => a ~> Array l).
Proof using (All).
xcf.
xpullpure H1.
xletopaque tmp Htmp.
evar (ty_ls: Type).
evar (ls: ty_ls).
xapp (Common.Verify_sseq.fold_spec tmp (0, nil) s ?ls (fun '((i, acc): (int * list (A))) (x: A) => ((i + 1), x :: acc))).
sep_solve.
eauto.
clear ty_ls ls.
xdestruct len ls Hlenls.
rewrite list_fold_length_rev in Hlenls.
injection Hlenls; intros Hls Hlen.
case ls as [ | init rest] eqn:H_eqn.
- xmatch.
xvalemptyarr.
{ symmetry; apply nil_eq_rev_inv; auto. }
- xmatch.
xalloc a data Hdata.
xletopaque idx Hidx.
xletopaque tmp0 Htmp0.
xapp (Common.Verify_list.list_fold_spec (tmp0) (idx) (rest)
        (fun (arg0: list (A))
             (arg1: int) =>
           \[ (arg1 = (((length (rest)) + (length (rest)))
                       - ((length (l)) + (length (arg0))))) ]
             \* a ~> CFML.WPArray.Array ((make (((length (rest)) - (length (arg0))))
                                            (init)) ++
                                           (drop ((length (rest))) ((arg0 ++ l)))))).
{ intros acc x t r Htxr.
  apply Htmp0.
  xpull;=> Heq.
  xapp. {
    apply int_index_prove.
    rewrite Heq, <- (length_rev l), <- Hls, !Htxr; rew_list; math.
    rewrite <- length_eq, Heq, <- (length_rev l), <- Hls, !Htxr; rew_list.
    rewrite length_make; math.
  }
  xvals*.
  rewrite Heq, <- (length_rev l), <- Hls, !Htxr; rew_list; math.
  rew_list.
  math_rewrite (length rest - length t = (length rest - length t - 1) + 1).
  math_rewrite (length rest - (1 + length t) = length rest - length t - 1).
  rewrite make_succ_r; try (rewrite Htxr; rew_list; math).
  rewrite app_last_l, update_middle;
    [ | rewrite Heq, <- (length_rev l), <- Hls,  length_make; rewrite !Htxr; rew_list; math ].
  rewrite Htxr; rew_list.
  rewrite drop_app_r; try math.
  rewrite drop_app_r; try math.
  math_rewrite ((length t + (1 + length r) - length t) = length r + 1).
  rewrite drop_cons; try math.
  apply (@f_equal (list A) (list A) (@rev A)) in Hls.
  rewrite rev_rev, rev_cons, Htxr in Hls; rew_list in Hls.
  f_equal.
  rewrite <- Hls.
  rewrite drop_app_r; rew_list; try math.
  math_rewrite ( (length r + 1 - length r) = 0 + 1).
  rewrite drop_app_r; rew_list; try math.
  math_rewrite ( (length r - length r) = 0).
  rewrite drop_cons, !drop_zero; try math.
  auto.
}
{ rewrite Hidx, Hlen, <- (length_rev l), <- Hls; rew_list; math. }
{ rew_list.
  math_rewrite (length rest - 0 = length rest).
  rewrite Hdata.
  apply (@f_equal (list A) (list A) (@rev A)) in Hls.
  rewrite rev_rev, rev_cons in Hls; rew_list in Hls.
  rewrite Hlen, <- Hls.
  rewrite drop_app_r; rew_list; try math.
  math_rewrite ((length rest - length rest) = 0).
  rewrite drop_zero.
  math_rewrite (1 + length rest = length rest + 1).
  rewrite make_succ_r; auto.
  pose proof (length_nonneg rest); math.
}
try xdestruct.
xvals*. {
  rewrite drop_app_r; try math.
  math_rewrite ((length rest - length rest) = 0).
  rewrite drop_zero, make_zero; auto.
}
Qed.
