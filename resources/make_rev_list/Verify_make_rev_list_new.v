Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsMakeRevList Require Import Verify_make_rev_list_utils.
From ProofsMakeRevList Require Import Make_rev_list_new_ml.
From ProofsMakeRevList Require Import Common_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (l:list A),
  SPEC (make_rev_list l)
    PRE (\[])
    POST (fun l' => \[l' = rev l]).
Proof using (All).
  xcf.
  
Admitted.
