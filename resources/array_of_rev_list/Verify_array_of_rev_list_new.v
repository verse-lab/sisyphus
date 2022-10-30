Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From Common Require Import Utils Solver Tactics. 

From Common Require Import Verify_combinators. 
From Common Require Import Verify_list. 

From ProofsArrayOfRevList Require Import Array_of_rev_list_new_ml.

Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
xcf.
case l as [ | x tl] eqn:H_eqn.
- xmatch.
xvalemptyarr.
- xmatch.
xletopaque len Hlen.
xalloc a data Hdata.
xletopaque tmp Htmp.
xapp (@list_ml_iteri_spec _ _ tmp (x :: tl)
        (fun (t: list A) =>
           a ~> Array ((make (length l - (length t)) x) ++ (take (length t) (rev t)))
        )
     ). { sis_generic_solver; try math. } { sis_generic_solver. }
xmatch.
xvals*. { sis_generic_solver. }
Qed.

