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

Lemma not_is_some_eq (A: Type) (x: option A):
  is_some x = false -> x = None.
Proof.
  case x as [vl|]; simpl; intros; auto.
  inversion H.
Qed.

Lemma is_some_ex (A: Type) (x: option A):
  is_some x = true -> exists (vl: A), x = Some vl.
Proof.
  case x as [vl|]; simpl; intros H; auto; try inversion H.
  exists vl; auto.
Qed.

Definition option_value (A: Type) (default: A) (vl: option A) : A :=
  match vl with
  | None => default
  | Some vl => vl
  end.

Definition option_value_fst (A B: Type) (default: A) (vl: option (A * B)) : A :=
  match vl with
  | None => default
  | Some (vl, _) => vl
  end.

Definition option_value_snd (A B: Type) (default: B) (vl: option (A * B)) : B :=
  match vl with
  | None => default
  | Some (_, vl) => vl
  end.
