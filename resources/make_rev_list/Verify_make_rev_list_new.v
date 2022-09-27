Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibList.

From ProofsMakeRevList Require Import Verify_make_rev_list_utils.
From ProofsMakeRevList Require Import Make_rev_list_new_ml.

Lemma make_rev_list_spec : forall A `{EA:Enc A} (ls:list A),
  SPEC (make_rev_list ls)
    PRE (\[])
    POST (fun l' => \[l' = rev ls]).
Proof using (All).
  xcf.
  xletopaque tmp Htmp.
  evar (a: A).
  evar (I : list A -> list A -> hprop).
  evar (Hf: (forall (acc : list A) (v : A) (t r : list A),
        (a :: nil) = t ++ v :: r ->
        SPEC (tmp acc v)
        PRE ?I t acc
        POST (fun acc0 : list A => ?I (t & v) acc0))).
  xapp (ProofsMakeRevList.Verify_make_rev_list_utils.list_fold_spec tmp nil ls
          (fun (t: list A) (acc: list A) => \[acc = rev t])). {
    intros acc v t r Hls; apply Htmp.
    xpullpure Hacc.
    xvals*.
    rew_list; rewrite Hacc.
    auto.
  } { rew_list. auto. }
  xvals*.
Admitted.
