Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Queue_ml.
From Common Require Import Utils.
From Common Require Import Tactics.

Definition Queue {A: Type} `{EA: Enc A} (ls: list A) (q: loc) :=
  \exists l r, \[ ls = r ++ l ] \*
  q ~~~> `{
    size'  := length ls;
    left'  := rev l;
    right' := r
  }.

Definition queue := fun (A: Type) => loc.

Lemma Queue_unfold {A: Type} `{EA: Enc A} (ls: list A) (q: queue A):
  q ~> Queue ls =
    \exists l r,
        \[ ls = r ++ l ] \*
          q ~~~> `{
            size'  := length ls;
            left'  := rev l;
            right' := r
          }.
Proof. unfold Queue; rewrite repr_eq; xsimpl*. Qed.
Arguments Queue_unfold [A] {EA} ls q.

Lemma queue_init_spec  {A: Type} `{EA: Enc A}:
  SPEC_PURE (queue_init tt)
    POST (fun (q: queue A) =>
            q ~> Queue (@nil A)
    ).
Proof.
  xcf.
  xapp;=> q.
  rewrite Queue_unfold; xsimpl*; rew_list; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec queue_init) => Provide queue_init_spec.

Lemma queue_enqueue_spec {A: Type} `{EA: Enc A}
  (q: queue A) (hd: A)
  (ls: list A):
  SPEC (queue_enqueue q hd)
    PRE (q ~> Queue ls)
    POSTUNIT (q ~> Queue (ls & hd)).
Proof.
  xcf.
  xchange Queue_unfold; xpull;=> l r Hlr.
  xapp.
  xapp.
  xapp.
  xapp.
  rewrite Queue_unfold.
  xsimpl*; rewrite Hlr; rew_list; auto; try math.
  rewrite rev_last; simpl; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec queue_enqueue) => Provide queue_enqueue_spec.

Lemma queue_dequeue_spec {A: Type} `{EA: Enc A}
  (q: queue A)
  (hd: A) (ls: list A):
  SPEC (queue_dequeue q)
    PRE (q ~> Queue (hd :: ls))
    POST (fun (res: A) => \[res = hd] \* q ~> Queue ls).
Proof.
  xcf.
  xassert.
  - xchange Queue_unfold; xpull;=> l t Hlr.
    xapp.
    xvals; rew_list; try math.
    rewrite Queue_unfold; xsimpl*; rew_list; math.
  - xchange Queue_unfold; xpull;=> l t Hlr.
    xapp.
    xapp.
    xapp.
    xmatch.
    + xapp.
      xlet.
      xmatch.
      * xapp.
        xapp.
        xvals;
          rew_list in Hlr; rewrite rev_rev, <- Hlr in TEMP; inversion TEMP; auto.
        rewrite Queue_unfold; xsimpl*.
        instantiate (1 := nil); rew_list; auto.
        rew_list; math.
        rew_list; auto.
      * rew_list in Hlr; rewrite rev_rev in TEMP; rewrite <- TEMP in Hlr; inversion Hlr.
    + xapp.
      xvals*.
      rew_list in *; inversion Hlr; auto.
      rewrite Queue_unfold; xsimpl*.
      rew_list in *; inversion Hlr; auto.
      rew_list; auto; math.
Qed.
#[export] Hint Extern 1 (RegisterSpec queue_dequeue) => Provide queue_dequeue_spec.

Lemma queue_iter_spec {A: Type} `{EA: Enc A}
  (f: func) (q: queue A) (I: list A -> hprop) (ls: list A) :
  (forall (v: A) (t r: list A),
      ls = t & v ++ r ->
      SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
  SPEC(queue_iter f q)
    PRE (q ~> Queue ls \* I nil)
    POST (fun (_: unit) => q ~> Queue ls \* I ls).
Proof.
  xcf.
  xchange Queue_unfold; xpull;=> l r Hlr.
  xapp.
  xlet.
  xapp.
  xapp.
  xapp.
  xlet as;=> loop Hloop.
  assert (forall (t r: list A),
             ls = t ++ r ->
             SPEC (loop r)
               PRE (I t)
               POSTUNIT (I ls)). {
    intros t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r' Htr.
    apply Hloop; clear Hloop.
    case_eq r'; [intros Hnil | intros rh rt Hrht].
    - xmatch. xvals*. subst; rew_list; xsimpl*; rew_list in Htr; subst; xsimpl*.
    - xmatch.
      xapp (H rh t rt); try (subst; rew_list; auto; math).
      xapp (IH (len + 1)); try apply upto_intro; try (subst; rew_list; auto; math).
      rewrite Hlen, Htr, Hrht; rew_list; math.
      xsimpl*.
  }
  xapp.
  xapp; rew_list; auto.
  rewrite Prev_left, rev_rev; auto.
  xsimpl*.
  rewrite Prev_left, rev_rev; rew_list; auto.
  rewrite Queue_unfold; xsimpl*.
  instantiate (1 := nil); rew_list; auto.
  rew_list; auto.
Qed.
Arguments queue_iter_spec {A} {EA} f q I ls Hf.
#[export] Hint Extern 1 (RegisterSpec queue_iter) => Provide queue_iter_spec.

Lemma queue_affine {A: Type} `{EA: Enc A}
  (s: queue A) (ls: list A): haffine (s ~> Queue ls).
Proof.
  unfold Queue; rewrite repr_eq.
  apply haffine_hexists; unfold haffine_post;=> vl.
  apply haffine_hexists; unfold haffine_post;=> vl'.
  apply haffine_hstar. apply haffine_hpure.
  apply haffine_Record.
Qed.
