Set Implicit Arguments.
Generalizable Variables A EA.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Stack_ml.
From Common Require Import Utils.
From Common Require Import Tactics.

Definition Stack {A: Type} `{EA: Enc A} (ls: list A) (s: loc) :=
  s ~~~> `{
      size' := length ls;
      elements' := ls
    }.

Definition stack := fun (A: Type) => loc.


Lemma Stack_unfold {A: Type} `{EA: Enc A} (ls: list A) (s: loc):
  s ~> Stack ls = s ~~~> `{ size' := length ls; elements' := ls }.
Proof. unfold Stack; rewrite repr_eq; xsimpl*. Qed.
Arguments Stack_unfold [A] {EA} ls s.

Lemma stack_init_spec {A: Type} `{EA: Enc A}:
  SPEC(stack_init tt)
    PRE \[]
    POST (fun (s: stack A) => s ~> Stack (@nil A)).
Proof.
  xcf.
  xapp.
  intros r.
  unfold Stack; rewrite (repr_eq (fun _ => _ ~~~> _)); xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec stack_init) => Provide stack_init_spec.
  
Lemma stack_size_spec {A: Type} `{EA: Enc A} (s: stack A) (ls: list A):
  SPEC(stack_size s)
    PRE (s ~> Stack ls)
    POST (fun (sz: int) => \[ sz = length ls ] \* s ~> Stack ls).
Proof.
  xcf; auto.
  xchange Stack_unfold.
  xapp.
  xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec stack_size) => Provide stack_size_spec.

Lemma stack_pop_spec {A: Type} `{EA: Enc A} (s: stack A) (hd: A) (tl: list A):
  SPEC(stack_pop s)
    PRE (s ~> Stack (hd :: tl))
    POST (fun (res: A) => \[ res = hd ] \* s ~> Stack tl).
Proof.
  xcf; auto.
  xchange Stack_unfold.
  xassert.
  xgo*; rew_list; math.
  xgo*.
  rewrite Stack_unfold; xsimpl*.
  rew_list; math.
Qed.
#[export] Hint Extern 1 (RegisterSpec stack_pop) => Provide stack_pop_spec.

Lemma stack_push_spec {A: Type} `{EA: Enc A} (s: stack A) (hd: A) (tl: list A):
  SPEC(stack_push s hd)
    PRE (s ~> Stack tl)
    POST (fun (_: unit) => s ~> Stack (hd :: tl)).
Proof.
  xcf; auto.
  xchange Stack_unfold.
  xgo*.
  rewrite Stack_unfold.
  xgo*.
  rew_list; math.
Qed.
#[export] Hint Extern 1 (RegisterSpec stack_push) => Provide stack_push_spec.
  
Lemma stack_clear_spec {A: Type} `{EA: Enc A} (s: stack A) (tl: list A):
  SPEC(stack_clear s)
    PRE (s ~> Stack tl)
    POST (fun (_: unit) => s ~> Stack (@nil A)).
Proof.
  xcf; auto. 
  xchange Stack_unfold.
  xgo*.
Qed.
#[export] Hint Extern 1 (RegisterSpec stack_clear) => Provide stack_clear_spec.

Lemma stack_iter_spec {A: Type} `{EA: Enc A} (f: func) (s: stack A)
  (I: list A -> hprop) (ls: list A) :
  (forall (v: A) (t r: list A),
      ls = t & v ++ r ->
      SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
  SPEC(stack_iter f s)
    PRE (s ~> Stack ls \* I nil)
    POST (fun (_: unit) => s ~> Stack ls \* I ls).
Proof.
  intros Hf.
  xcf.
  xlet as;=> loop Hloop.
  assert (forall (t r: list A),
             ls = t ++ r ->
             SPEC (loop r)
               PRE (I t)
               POSTUNIT (I ls)). {
    intros t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r Htr.
    apply Hloop; clear Hloop.
    case_eq r; [intros Hnil | intros rh rt Hrht].
    - xmatch. xvals*. subst; rew_list; xsimpl*.
    - xmatch.
      xapp (Hf rh t rt); try (subst; rew_list; auto; math).
      xapp (IH (len + 1)); try apply upto_intro; try (subst; rew_list; auto; math).
      xsimpl*.
  }
  xchange Stack_unfold.
  xapp.
  xapp; rew_list; auto.
  xsimpl*.
Qed.
Arguments stack_iter_spec {A} {EA} f s I ls Hf : rename.
#[export] Hint Extern 1 (RegisterSpec stack_iter) => Provide stack_iter_spec.

Lemma stack_drain_spec {A: Type} `{EA: Enc A} (f: func) (s: stack A)
  (I: list A -> hprop) (ls: list A):
  (forall (v: A) (t r: list A),
      ls = t & v ++ r ->
      SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
  SPEC(stack_drain f s)
    PRE (s ~> Stack ls \* I nil)
    POST (fun (_: unit) => s ~> Stack (@nil A) \* I ls).
Proof.
  intros Hf.
  cut (
      forall (t r : list A),
        ls = t ++ r ->
        SPEC (stack_drain f s)
          PRE s ~> @Stack A EA r \* I t
          POSTUNIT (s ~> @Stack A EA nil \* I ls)
    ). {
    intros H.
    apply (H nil ls); rew_list; auto.
  }
  intros t; remember (length t) as len; gen t.
  induction_wf IH: (upto (length ls)) len; intros t Hlen r Heq; xcf.
  xapp.
  case_eq r; [intros Hnil | intros rh rt Hreq].
  - rew_list; xif; try (intros; math).
    intros _.
    xvals*.
    subst; rew_list; xsimpl*.
  - rew_list; xif; try (intros; math).
    intros Hgt.
    xapp.
    xapp (Hf rh t rt); try (subst; rew_list; auto; math).
    xapp (IH (len + 1)); try apply upto_intro; subst; rew_list; try math; auto.
    xsimpl*.
Qed.
Arguments stack_drain_spec {A} {EA} f s I ls Hf : rename.
#[export] Hint Extern 1 (RegisterSpec stack_drain) => Provide stack_drain_spec.

Lemma stack_affine {A: Type} `{EA: Enc A}
  (s: stack A) (ls: list A): haffine (s ~> Stack ls).
Proof.
    unfold Stack; rewrite repr_eq. apply haffine_Record.
Qed.
