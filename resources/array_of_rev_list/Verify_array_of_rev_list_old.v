Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_old_ml.

Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof.
  xcf.
  case l as [ | x l'] eqn: H.
  - xmatch_case_0.
    xapp. xsimpl.
  - xmatch.
    xletopaque len Hlen.
    xalloc arr data Hdata.
    xapp. intros r.
    xseq.
        (* xfor_inv (fun (i: int) => a ~> Array (take i a_l ++  take (length l - i) (rev l))) *)
        Abort.
