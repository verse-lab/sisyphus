Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibList.

From Common Require Import Utils Solver Tactics. 
From Common Require Import Verify_list. 

From ProofsMakeRevList Require Import Make_rev_list_new_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (ls:list A),
  SPEC (make_rev_list ls)
    PRE (\[])
    POST (fun l' => \[l' = rev ls]).
Proof using (All).
  xcf.
  xletopaque tmp Htmp.
  xapp (Common.Verify_list.list_fold_spec tmp nil ls
          (fun (t: list A) (acc: list A) => \[acc = rev t])). {
    sis_generic_solver. 
  } { sis_generic_solver. }
  xvals*.
Qed.
