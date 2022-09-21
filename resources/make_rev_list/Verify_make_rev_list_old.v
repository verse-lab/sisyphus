Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsMakeRevList Require Import Verify_make_rev_list_utils.
From ProofsMakeRevList Require Import Make_rev_list_old_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (make_rev_list l)
    PRE (\[])
    POST (fun l' => \[l' = rev l]).
Proof.
  xcf.
  xapp. intros r.
  xletopaque f Hf.
  xapp (@List_proof.iter_spec A EA l f
           (fun (ls : list A) => r ~~> rev ls)
       ). { intros. apply Hf. xapp. xapp. xsimpl*. rew_list. auto. }
  xmatch.
  xapp.
  xsimpl*.
Qed.
