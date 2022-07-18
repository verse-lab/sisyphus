Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList2 Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList2 Require Import Array_of_rev_list_new_ml.


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
    xletopaque f Hf.
    asserts Haux : (forall (i: int) (ls: list A),
        i = length l - length ls ->
        SPEC_PURE (f i ls)
                  POST (fun '((j, arr) : (credits * array A)) => \[j = length l] \* arr ~> Array (make i x  ++ rev (take (length l - i) l)))).
    {
      intros. gen i. induction_wf IH: list_sub ls; intros.
      apply Hf.
      case_eq ls; intros; rewrite H1 in H0; rew_list in H0.
      + xmatch. xapp; try math.  introv ->; xvals; try math.
        math_rewrite (length l - 0 = length l) in H0.
        rewrite <- H0 at 1. math_rewrite (i - i = 0). rew_list; auto.
      + xmatch. xapp; try math. rewrite H1; auto.
        intros [len arr]. xpull. intros. xmatch.
        asserts Hi: (i + 1 >= 0). { admit. }
        xapp. rewrite index_eq_index_length. apply int_index_prove; try math.
        rewrite length_app, length_make, length_rev, length_take; auto.
        admit.
        rewrite H0.
        math_rewrite (length l - (1 + length l0) + 1 = length l - length l0).
        rewrite <- H2.
        math_rewrite (len - (len - length l0) = length l0).
        rewrite H2.
        math.
        xvals; auto.
        admit.
    }
    xapp; auto. rewrite <- H; math. intros [num arr].
    xpullpure Hnum.
    xmatch. xvals. rewrite make_zero, app_nil_l, Z.sub_0_r, take_full_length, H; auto.
Admitted.
