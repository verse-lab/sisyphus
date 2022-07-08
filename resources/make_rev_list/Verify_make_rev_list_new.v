Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsMakeRevList Require Import Verify_make_rev_list_utils.
From ProofsMakeRevList Require Import Make_rev_list_new_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (make_rev_list l)
    PRE (\[])
    POST (fun l' => \[l' = rev l]).
Proof.
  xcf.
  xletopaque f Hf.
  xapp (list_fold_spec f nil l
                       (fun (ls: list A) (acc: list A) => \[rev ls = acc])
       ). { intros. apply Hf. xpullpure Hl.  xval. xsimpl. rew_list. subst. reflexivity.} { auto. }
  xsimpl.
  auto.
Qed.
