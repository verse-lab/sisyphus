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
xapp (Common.Verify_tree.tree_fold_spec tmp (0, nil) t  (fun '((i, acc): (int * list (A))) (vl: A) => ((i + 1), vl :: acc))).
sep_solve.
clear .
xdestruct len elts Hlenelts.
rewrite list_fold_length_rev in Hlenelts.
injection Hlenelts; intros Helts Hlen.
xalloc arr data Hdata.
xletopaque idx Hidx.
xletopaque tmp0 Htmp0.
xapp (Common.Verify_list.list_fold_spec (tmp0) (idx) (elts) (fun (l: list (A)) (i: int) => \[ (i = ((idx - idx) + (idx - (length (l))))) ]  \* arr ~> CFML.WPArray.Array ((nil ++ (drop ((idx - i)) (((make ((length (elts))) ((thead (t)))) ++ (rev (l))))))))).
{
  sis_generic_solver; rewrite <- (length_rev (tol t)); rewrite x; sis_generic_solver.
  rewrite !drop_app_l; sis_normalize_length.
  sis_generic_solver.
  math_rewrite (length t0 + length r + 1 - (length t0 + length r - length r) = length r + 1).
  math_rewrite (length t0 + length r - (length r - 1) = length t0 + 1).
  sis_generic_solver.
}
{
sis_generic_solver.
}
{
sis_generic_solver.
}
intros unused Hunused.
try xdestruct.
xvals.
{
 sis_generic_solver.
 math_rewrite ((length (tol t) - 1 - (length (tol t) - 1 - length (tol t)) - length (tol t)) = 0).
 sis_generic_solver.

}
Qed.
