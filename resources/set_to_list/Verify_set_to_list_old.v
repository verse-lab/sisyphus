Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.

From Common Require Import Verify_set.


From ProofsSetToList Require Import Set_to_list_old_ml.

Lemma set_to_list_spec :
  forall (s : intset) (ls : list int),
  SPEC (set_to_list s)
  PRE (s ~> Intset ls)
  POST (fun (res : list int) => \[ res = ls ] \* s ~> Intset ls ).
Proof using (All).
  xcf.
  xref l.
  xletopaque tmp Htmp.
  xapp (set_iter_spec tmp s
          (fun (ls: list int) =>
          l ~~> rev ls   
       )). {
    sis_solve_start; rew_list; auto.
  }
  xmatch.
  xapp.
  xletopaque rev Hrev.
  xvals*. { subst; rew_list; auto. }
Qed.
