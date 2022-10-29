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
    sis_generic_solver; sis_tree_solver.
    } { sis_generic_solver. } { sis_generic_solver. } 
  intros unused Hunused.
  xmatch.
  xvals. { sis_generic_solver. }
Qed.
