Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_old_ml.

Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
  xcf.
  case l as [ | x l'] eqn: H.
  - xmatch_case_0.
    xapp Array_proof.of_list_spec. xsimpl.
  - xmatch.
    xletopaque len Hlen.
    xalloc arr data Hdata.
    xapp (ref_spec l'). intros r.
    xletopaque loop Hloop.
    asserts Hrec : (forall i : int, -1 <= i <= len - 2 ->
                                SPEC (loop i)
                                     PRE (r ~> Ref (drop (len - (i + 1)) l)
                                            \*
                                            arr ~> Array (take (i + 1) data ++ rev (take (len - (i + 1)) l)) )
                                     POSTUNIT (r ~>  Ref (drop len l)
                                                 \*
                                                 arr ~> Array (rev l))).
    { admit. }

    (* now, we reason about the loop *)
    xapp Hrec. { admit. }  { admit. }  { admit. }
    xmatch.
    xvals. { admit. }
Admitted.
