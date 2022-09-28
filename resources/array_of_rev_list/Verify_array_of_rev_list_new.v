Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_new_ml.

Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
Admitted.
