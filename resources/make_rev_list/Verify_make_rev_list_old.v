Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Utils Solver Tactics. 
From Common Require Import Verify_list. 

From ProofsMakeRevList Require Import Make_rev_list_old_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (ls:list A),
  SPEC (make_rev_list ls)
    PRE (\[])
    POST (fun l' => \[l' = rev ls]).
Proof.
  xcf.
  xref r.
  xletopaque f Hf.
  xapp (list_iter_spec f ls
           (fun (ls' : list A) => r ~~> rev ls')
       ). { sis_generic_solver.  }
  xunit.
  xsimpl*.
Qed.
