Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.

From Common Require Import Verify_set.

From ProofsSetToList Require Import Set_to_list_new_ml.

Lemma set_to_list_spec :
  forall (s : intset) (ls : list int),
  SPEC (set_to_list s)
  PRE (s ~> Intset ls)
  POST (fun (res : list int) => \[ res = ls ] \* s ~> Intset ls ).
Proof using (All).
  xcf.
  xletopaque tmp Htmp.
  xapp (set_fold_spec tmp nil s
          (fun (ls: list int) (acc: list int) =>
             \[acc = rev ls]
       )). {
    sis_solve_start; subst; rew_list; auto.
  } { rew_list; auto. }
  intros res Hres.
  xlet.
  xvals*. { subst; rew_list; auto. }
Qed.
