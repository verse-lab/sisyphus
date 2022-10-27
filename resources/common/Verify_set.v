Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.


Require Import Set_ml.
From Common Require Import Utils.
From Common Require Import Tactics.

Definition Intset (ls: list int) (s: loc) :=
  s ~~> ls \* \[noduplicates ls].

Definition intset := loc.

Lemma Intset_unfold (ls: list int) (s: loc):
  s ~> Intset ls = s ~~> ls \* \[noduplicates ls].
Proof. unfold Intset; rewrite repr_eq; xsimpl*. Qed.
Arguments Intset_unfold ls s : clear implicits.

Lemma set_mem_spec (s: intset) (k: int) (ls: list int) :
  SPEC(set_mem k s)
    PRE (s ~> Intset ls)
    POST (fun (res: bool) => \[res = isTrue (mem k ls)] \* s ~> Intset ls).
Proof.
  xcf.
  xletopaque loop Hloop.
  assert (forall r,
             SPEC_PURE (loop r)
               POST (fun (res: bool) => \[res = isTrue (mem k r)])
         ). {
    induction r; xapp (Hloop); clear Hloop; xgo*.
    rewrite mem_nil_eq; auto.
    rewrite Px0__, istrue_isTrue_eq in H; rewrite H; apply mem_cons_l.
    rewrite Px0__, istrue_isTrue_eq in H;
      split; intros Hmem; try apply mem_cons_r; auto; apply mem_cons_inv in Hmem;
      destruct Hmem as [Heq|Hneq]; subst; auto; contradiction H; auto.
  }
  xchange Intset_unfold;=> Hndup.
  xapp.
  xapp.
  xsimpl*.
  rewrite Intset_unfold; xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec set_mem) => Provide set_mem_spec.

Lemma set_add_spec (s: intset) (k: int) (ls: list int) :
  ~ mem k ls ->
  SPEC(set_add k s)
    PRE (s ~> Intset ls)
    POST (fun (_: unit) => s ~> Intset (k :: ls)).
Proof.
  xcf.
  xassert.
  xapp (set_mem_spec).
  xvals*.
  xsimpl; xchange Intset_unfold;=> Hndup.
  xapp.
  xapp.
  rewrite Intset_unfold; xsimpl*.
  apply noduplicates_cons; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec set_add) => Provide set_add_spec.

Lemma set_fold_spec :
  forall {A: Type} `{EA: Enc A}
         (f: func) (init: A) (s: intset),
  forall (I: list int -> A -> hprop) (ls: list int),
    (forall (acc: A) (v: int) (t r: list int),
        (ls = t++v::r) ->
        SPEC (f acc v)
          PRE (I t acc)
          POST (fun acc => I (t&v) acc)) ->
    SPEC (set_fold f init s)
      PRE (s ~> Intset ls \* I nil init)
      POST (fun acc => s ~> Intset ls \* I ls acc).
Proof using.
  intros A EA f init s I ls Hf.
  xcf.
  xlet as;=> loop Hloop.
  assert (forall r t init,
             ls = t ++ r ->
             SPEC (loop init r)
               PRE I t init
               POST (fun (acc : A) => I ls acc)). {
    intros r; induction_wf IH: list_sub r.
    intros t acc Hls.
    apply Hloop; clear Hloop.
    xmatch.
    - xvals*.
      subst; rew_list; xsimpl*.
    - xapp (Hf acc h); try (subst; auto; math).
      intros acc'.
      xapp; try apply list_sub_cons; try (subst; rew_list; auto; math).
      intros res.
      subst; xsimpl*.
  }
  clear Hloop.
  xchange Intset_unfold; intros Hndup.
  xapp.
  xapp; rew_list; auto.
  rewrite Intset_unfold; intros; xsimpl*.
Qed.
Arguments set_fold_spec {A} {EA} f init s I ls Hf.
#[export] Hint Extern 1 (RegisterSpec set_fold) => Provide set_fold_spec.

Lemma set_iter_spec (f: func) (s: intset)
  (I: list int -> hprop) (ls: list int) :
  (forall (v: int) (t r: list int),
      ls = t & v ++ r ->
      SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
  SPEC(set_iter f s)
    PRE (s ~> Intset ls \* I nil)
    POST (fun (_: unit) => s ~> Intset ls \* I ls).
Proof.
  intros Hf.
  xcf.
  xlet as;=> loop Hloop.
  assert (forall (t r: list int),
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
  xchange Intset_unfold;=> Hndup.
  xapp.
  xapp; rew_list; auto.
  rewrite Intset_unfold; xsimpl*.
Qed.
Arguments set_iter_spec f s I ls Hf : clear implicits.
#[export] Hint Extern 1 (RegisterSpec set_iter) => Provide set_iter_spec.

