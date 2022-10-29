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
       ). { sis_generic_solver; sis_tree_solver. }
  xmatch.
  xvals*. { sis_generic_solver; sis_tree_solver. }
Qed.
