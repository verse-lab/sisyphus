Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Opt_ml.


Lemma opt_is_some_spec : forall (A:Type) `{EA: Enc A} (v: option A),
    SPEC_PURE (option_is_some v)
      POST (fun (b: bool) => \[b = is_some v]).
Proof.
  intros; xcf.
  xmatch.
  - xvals*.
  - xvals*. 
    unfold Wpgen_negpat in C.
    destruct v; simpl; auto.
    pose proof (C a).
    contradiction H; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec option_is_some) => Provide opt_is_some_spec.

Lemma opt_is_none_spec : forall (A:Type) `{EA: Enc A} (v: option A),
    SPEC_PURE (option_is_none v)
      POST (fun (b: bool) => \[b = negb (is_some v)]).
Proof.
  intros; xcf.
  xmatch.
  - xvals*.
  - xvals*. 
    unfold Wpgen_negpat in C.
    destruct v; simpl; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec option_is_none) => Provide opt_is_none_spec.

