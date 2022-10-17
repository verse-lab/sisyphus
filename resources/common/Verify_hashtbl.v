Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.


Require Import Hashtbl_ml.
From Common Require Import Utils.
From Common Require Import Tactics.


Definition Hashtbl {A: Type} `{EA: Enc A} (ls: list (int * A)) (h: loc) :=
  h ~~~> `{
      size' := length ls;
      elements' := ls
    } \* \[noduplicates ls].

Definition hashtbl := (fun (A: Type) => loc).



Lemma Hashtbl_unfold  {A: Type} `{EA: Enc A} (ls: list (int * A)) (h: loc):
  h ~> Hashtbl ls = 
    h ~~~> `{
        size' := length ls;
        elements' := ls
      } \* \[noduplicates ls].
Proof. unfold Hashtbl; rewrite repr_eq; xsimpl*. Qed.

Lemma hashtbl_create_spec  {A: Type} `{EA: Enc A} :
  SPEC_PURE (hashtbl_create tt)
    POST (fun (h: hashtbl A) => h ~> Hashtbl (@nil (int * A))).
Proof.
  xcf.
  xapp.
  intros r.
  rewrite Hashtbl_unfold; xsimpl*.
  apply noduplicates_nil.
Qed.
#[export] Hint Extern 1 (RegisterSpec hashtbl_create) => Provide hashtbl_create_spec.


Lemma hashtbl_remove_spec  {A: Type} `{EA: Enc A}
  (tbl: hashtbl A) (key: int) (ls: list (int * A)):
  SPEC (hashtbl_remove tbl key)
    PRE (tbl ~> Hashtbl ls)
    POSTUNIT (tbl ~> Hashtbl (filter_first key ls)).
Proof.
  xcf.
  xlet as;=> loop Hloop.
  rewrite Hashtbl_unfold; xpull;=> Hndup.
  assert (forall (r: list (int * A)) (i: int),
             i =  count (fun '(k', _) => ~ (key = k')) ls + count (fun '(k', _) => key = k') r ->
             SPEC (loop r)
               PRE (tbl ~~~> `{ size' := i; elements' := ls})
               POST (fun (res: list (int * A)) =>
                       \[ res = filter_first key r ] \*
                         tbl ~~~> `{
                           size' := count (fun '(k', _) => ~ (key = k')) ls;
                           elements' := ls
                         }
               )
         ). {
    intros r; induction_wf IH: list_sub r; intros i Hi.
    apply Hloop; clear Hloop.
    xmatch.
    - xvals*; rewrite count_nil in Hi; rewrite Hi; math.
    - xlet as;=> cond Hcond_eq.
      xif;=> Hres; rewrite Hcond_eq, istrue_isTrue_eq in Hres.
      + xapp.
        xapp.
        xapp; try apply list_sub_cons.
        rewrite Hi, count_cons; destruct h as [hi hvl]; simpl in *; subst; rewrite If_l; auto; math.
        xsimpl*.
        unfold filter_first; rew_list; rewrite filter_cons;
          destruct h as [hi hvl]; simpl in *; subst; rewrite If_r; auto.
      + xapp; try apply list_sub_cons.
        rewrite Hi, count_cons; destruct h as [hi hvl]; simpl in *; subst; rewrite If_r; auto; math.
        xvals*.
        unfold filter_first; rew_list; rewrite filter_cons;
          destruct h as [hi hvl]; simpl in *; subst; rewrite If_l; auto.
  }
  xapp.
  xapp; try rewrite (count_split ls (fun k => key = k)); auto; try math.
  xapp.
  rewrite Hashtbl_unfold; xsimpl*.
  unfold filter_first; rewrite !count_eq_length_filter; auto.
  unfold filter_first; apply noduplicates_filter; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec hashtbl_remove) => Provide hashtbl_remove_spec.

Lemma hashtbl_add_spec {A: Type} `{EA: Enc A} (tbl: hashtbl A) (key: int) (v: A) (ls: list (int * A)):
  ~ mem (key, v) ls ->
  SPEC (hashtbl_add tbl key v)
    PRE (tbl ~> Hashtbl ls)
    POSTUNIT (tbl ~> Hashtbl ((key, v) :: ls)).
Proof.
  intros Hmem.
  xcf.
  rewrite Hashtbl_unfold; xpull;=> Hnodup.
  xapp.
  xapp.
  xapp.
  xapp.
  rewrite Hashtbl_unfold; xsimpl*.
  rew_list; math.
  apply noduplicates_cons; auto.
Qed.
#[export] Hint Extern 1 (RegisterSpec hashtbl_add) => Provide hashtbl_add_spec.
    
Lemma hashtbl_fold_spec :
  forall  {A: Type} `{EA: Enc A} {B: Type} `{EB: Enc B}
          (tbl: hashtbl A) (f: func) (init: B),
  forall (I: list (int * A) -> B -> hprop) (ls: list (int * A)),
    (forall (acc: B) (v: (int * A)) (t r: list (int * A)),
        (ls = t++v::r) ->
        SPEC (f acc v)
          PRE (I t acc)
          POST (fun acc => I (t&v) acc)) ->
    SPEC (hashtbl_fold tbl f init)
      PRE (tbl ~> Hashtbl ls \* I nil init)
      POST (fun acc => tbl ~> Hashtbl ls \* I ls acc).
Proof using.
  intros A EA B EB tbl f init I ls Hf.
  xcf.
  xlet as;=> loop Hloop.
  assert (forall (r t: list (int * A)) (init: B),
             ls = t ++ r ->
             SPEC (loop init r)
               PRE I t init
               POST (fun (acc : B) => I ls acc)). {
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
  rewrite Hashtbl_unfold; xpull; intros Hndup.
  xapp.
  xapp; rew_list; auto;=> res; xvals*; xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec hashtbl_fold) => Provide hashtbl_fold_spec.

Lemma hashtbl_iter_spec {A: Type} `{EA: Enc A} (tbl: hashtbl A) (f: func) 
  (I: list (int * A) -> hprop) (ls: list (int * A)) :
  (forall (v: (int * A)) (t r: list (int * A)),
      ls = t & v ++ r ->
      SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
  SPEC(hashtbl_iter tbl f)
    PRE (tbl ~> Hashtbl ls \* I nil)
    POST (fun (_: unit) => tbl ~> Hashtbl ls \* I ls).
Proof.
  intros Hf.
  xcf.
  xlet as;=> loop Hloop.
  assert (forall (t r: list (int * A)),
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
  rewrite Hashtbl_unfold; xpull;=> Hndup.
  xapp.
  xapp; rew_list; auto; xsimpl*; xvals*.
Qed.
#[export] Hint Extern 1 (RegisterSpec hashtbl_iter) => Provide hashtbl_iter_spec.
