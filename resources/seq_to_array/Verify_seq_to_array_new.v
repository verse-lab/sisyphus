Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sseq.
From Common Require Import Verify_list.

From Common Require Import Tactics.
From Common Require Import Solver.
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
Check (Common.Verify_sseq.fold_spec).
Check (Common.Verify_sseq.fold_spec tmp (0, nil) s ?ls (fun '((i, acc): (int * list (A))) (x: A) => ((i + 1), x :: acc))).
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
{
sis_generic_solver.
}
- xmatch.
xalloc a data Hdata.
xletopaque idx Hidx.
xletopaque tmp0 Htmp0.
xapp (Common.Verify_list.list_fold_spec (tmp0) (idx) (rest)
        (fun (t: list (A)) (i: int) =>
           \[ (i = ((idx - idx) + (idx - (length (t))))) ]
             \* a ~> CFML.WPArray.Array (((drop ((length (t))) ((make ((length (rest))) (init)))) ++ (drop ((i + len)) ((rest ++ (rev (ls))))))))).
{

  sis_generic_solver; rew_list; auto.

   math_rewrite (length r + (length t + length r) + 1 = length t + 1 + length r + length r).
  repeat (rewrite drop_app_r; try math).
  math_rewrite (length t  + 1 + length r + length r + 1 - length t = length t  + 1 + length r + length r - length t + 1).
  math_rewrite (length t  + 1 + length r + length r - length t = 1 + length r + length r).
  rewrite! (drop_app_r (v0 :: r) (rev r ++ v0 :: rev t & init)); try (rewrite length_cons; math).
  rewrite length_cons.
  math_rewrite (1 + length r + length r + 1 - (1 + length r) = length r + 1).
  math_rewrite (1 + length r + length r - (1 + length r) = length r).
  rewrite !drop_app_r; rew_list; try math.
  sis_simplify_math_goal.
  sis_list_solver; auto.


}
{
sis_generic_solver.
}
{ sis_generic_solver; rew_list; auto.
  subst; sis_list_solver.
  math_rewrite (length rest + 1 -2 + length rest + 1 = length rest + length rest).
  rewrite !drop_app_r; rew_list; try math.
  sis_generic_solver.
}
intros unused Hunused.
try xdestruct.
xvals.
{
  sis_generic_solver.
  math_rewrite (length rest + 1 - 2 - length rest + length rest + 1 = length rest).
  rewrite drop_app_r; try math; sis_generic_solver.
}
Qed.
