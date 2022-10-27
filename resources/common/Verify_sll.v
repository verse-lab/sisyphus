Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Sll_ml.
From Common Require Import Utils.
From Common Require Import Tactics.


Fixpoint SLL A `{EA: Enc A} (ls: list A) (l: loc) : hprop :=
  match ls with
  | h :: t => \exists (lt: loc), l ~~> Node h lt \* lt ~> SLL t
  | nil => l ~~> @Nil A
  end.

Fixpoint SLL_part A `{EA: Enc A} (ls: list A) (rst: loc) (l: loc) : hprop :=
  match ls with
  | h :: t => \exists (lt: loc), l ~~> Node h lt \* lt ~> SLL_part t rst
  | nil => \[l = rst]
  end.

Definition sll := fun A : Type => loc.

Lemma SLL_nil A `{EA: Enc A} (a: sll A):
  a ~> SLL (@nil A) = a ~~> @Nil A.
Proof. xsimpl*. Qed.
Arguments SLL_nil [A] {EA} a.

Lemma SLL_cons A `{EA: Enc A} (a: sll A) (h: A) (t : list A):
  a ~> SLL (h :: t) = \exists (lt: loc), a ~~> Node h lt \* lt ~> SLL t.
Proof. simpl SLL; rewrite repr_eq; xsimpl*. Qed.
Arguments SLL_cons [A] {EA} a h t.

Lemma SLL_fold_nil A `{EA: Enc A}  (new_a: loc):
  new_a ~~> @Nil A ==>
    new_a ~> @SLL A EA (@nil A).
Proof. simpl SLL. rewrite (repr_eq (fun _ => _ ~~> _)); xsimpl*. Qed.
Arguments SLL_fold_nil [A] {EA} new_a.

Lemma SLL_fold_cons A `{EA: Enc A} (hd: A) (t: list A) (a: sll A) (new_a: loc):
  a ~> SLL t \* new_a ~~> Node hd a ==>
    new_a ~> SLL (hd :: t).
Proof. simpl SLL. rewrite (repr_eq (fun _ => \exists _, _)); xsimpl*. Qed.
Arguments SLL_fold_cons [A] {EA} hd t a new_a.

Lemma SLL_part_nil A `{EA: Enc A} (a: sll A) (rst: sll A):
  a ~> SLL_part (@nil A) rst = \[a = rst].
Proof. simpl SLL_part; rewrite repr_eq; xsimpl*. Qed.

Lemma SLL_part_cons A `{EA: Enc A} (a: sll A) (h: A) (t : list A)
  (lst : loc):
  a ~> SLL_part (h :: t) lst = \exists (lt: loc), a ~~> Node h lt \* lt ~> SLL_part t lst.
Proof. simpl SLL_part; rewrite repr_eq; xsimpl*. Qed.

Lemma SLL_part_fold_cons A `{EA: Enc A} (hd: A) (t: list A) (a: sll A)
  (lst: loc) (new_a: loc):
  a ~> SLL_part t lst \* new_a ~~> Node hd a ==>
    new_a ~> SLL_part (hd :: t) lst.
Proof. simpl SLL_part. rewrite (repr_eq (fun _ => \exists _, _)); xsimpl*. Qed.

Lemma SLL_part_fold_last A `{EA: Enc A} (t: list A) (a: sll A) (lst: sll A):
  a ~> SLL_part t lst \* lst ~~> @Nil A ==>
    a ~> SLL t.
Proof.
  gen a lst; induction t as [| hd tl]; intros a lst.
  - simpl SLL_part; simpl SLL; rewrite !repr_eq.
    xsimpl*; intros ->; xsimpl*.
  - simpl SLL_part; simpl SLL; rewrite !repr_eq.
    xsimpl*;=> tl.
Qed.

Lemma SLL_part_fold_last_cons A `{EA: Enc A} (t: list A) (a: sll A) (v: A)
  (lst new_lst: sll A):
  a ~> SLL_part t lst \* lst ~~> Node v new_lst ==>
    a ~> SLL_part (t & v) new_lst.
Proof.
  gen a lst; induction t as [| hd tl]; intros a lst.
  - simpl SLL_part; simpl SLL; rewrite repr_eq.    
    xsimpl*; intros ->. rew_list; simpl SLL_part.
    rewrite (@repr_eq loc (fun l : loc => \exists _, _) lst).
    xsimpl.
    rewrite repr_eq; xsimpl*.
  - rew_list; simpl SLL_part; rewrite repr_eq; xpull; => hd_tl.
    rewrite (repr_eq (fun _ => \exists _, _)).
    xchange IHtl. xsimpl*.
Qed.                                             

Lemma SLL_part_unfold_last_cons A `{EA: Enc A} (t: list A) (a: sll A) (v: A)
  (lst: sll A):
  a ~> SLL_part (t & v) lst ==>
    \exists new_lst, a ~> SLL_part t new_lst \* new_lst ~~> Node v lst.
Proof.
  gen a lst; induction t as [| hd tl]; intros a lst.
  - rew_list; simpl SLL_part; rewrite repr_eq.
    xpull;=> new_lst.
    rewrite (repr_eq (fun _ => \[ _ ])).
    xpull; intros ->.
    xsimpl*.
    rewrite (repr_eq (fun _ => \[ _ ])).
    xsimpl*. 
  - rew_list; simpl SLL_part; rewrite repr_eq; xpull; => hd_ptr.
    xchange IHtl;=> new_lst.
    xsimpl*.
    rewrite (repr_eq (fun _ => \exists _, _)).
    xsimpl*.
Qed.

    
Lemma SSL_part_intro A `{EA: Enc A} (t: list A) (a: sll A):
  a ~> SLL t ==>
    \exists (lst: sll A),
      a ~> SLL_part t lst \* lst ~> SLL (@nil A).
Proof.
  gen a; induction t as [| hd tl]; intros a.
  - simpl SLL_part; simpl SLL; rewrite repr_eq.
    xsimpl*. rewrite repr_eq; xsimpl*.
  - simpl SLL; rewrite repr_eq; xpull; => hd_tl.
    xchange IHtl;=> lst.
    simpl SLL_part; xsimpl*.
    rewrite (repr_eq (fun _ => \exists _, _)).
    xsimpl*.
Qed.

Lemma SSL_part_intro_empty A `{EA: Enc A} (t: list A) (a: sll A):
  a ~> SLL t ==> a ~> SLL t \* a ~> SLL_part (@nil A) a.
Proof.
  simpl SLL_part. rewrite (repr_eq (fun _ => \[ _ ])).
  xsimpl*.
Qed.

Lemma sll_cons_spec :
  forall A `{EA: Enc A} (hd: A) (l: sll A) (ls: list A), 
         SPEC (sll_cons hd l)
         PRE (l ~> SLL ls)
         POST (fun (res: sll A) => res ~> SLL (hd :: ls)).
Proof.
  xcf.
  xapp; intros new_hd.
  xchange SLL_fold_cons.
  xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec sll_cons) => Provide sll_cons_spec.
  
Lemma sll_nil_spec :
  forall A `{EA: Enc A}, 
         SPEC (sll_nil tt)
         PRE \[]
         POST (fun (res: sll A) => res ~> @SLL A EA (@nil A)).
Proof.
  intros A EA.
  eapply sll_nil_cf__; (try exact EA).
  xapp; intros new_hd.
  xval.
  rewrite SLL_nil; xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec sll_nil) => Provide sll_nil_spec.

Lemma sll_push_spec :
  forall A `{EA: Enc A} (hd: A) (l: sll A) (ls: list A), 
         SPEC (sll_push hd l)
         PRE (l ~> SLL ls)
         POSTUNIT (l ~> SLL (hd :: ls)).
Proof.
  xcf.
  destruct ls as [| x xs].
  - xchange SLL_nil.
    xapp.
    xapp;=> new_tl.
    xapp.
    xchange SLL_fold_nil.
    xchange SLL_fold_cons.
    xsimpl*.
  - xchange SLL_cons.
    intros tl.
    xapp.
    xapp;=> new_tl.
    xapp.
    xchange SLL_fold_cons.
    xchange SLL_fold_cons.
    xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec sll_push) => Provide sll_push_spec.

Lemma sll_iter_spec :
  forall A `{EA: Enc A}
         (f: func) (l: sll A) 
         (I: list A -> hprop) (ls: list A),
         (forall t v r,
             ls = t & v ++ r ->
             SPEC (f v)
             PRE (I t)
             POSTUNIT (I (t & v))
         ) ->
         SPEC (sll_iter f l)
         PRE (l ~> SLL ls \* I nil)
         POSTUNIT (I ls \* l ~> SLL ls).
Proof.
  intros A EA f l I ls Hf.
  xcf.
  xlet as;=> aux Haux.
  assert (forall (t r : list A)  (node: sll A),
             ls = t ++ r ->
             SPEC (aux node)
             PRE (I t \* node ~> SLL r \* l ~> SLL_part t node)
             POSTUNIT (I ls \* l ~> SLL ls)
         ). {
    intro t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r node Hlstr.
    apply Haux; clear Haux.
    case_eq r; [intro Hnil | intros rv rt Heqr].
    - xchange SLL_nil. 
      xapp.
      xmatch.
      xvals*. { subst; rew_list; xsimpl*. xchange SLL_part_fold_last. xsimpl*. }
    - xchange SLL_cons. intros tl.
      xapp.
      xmatch.
      xapp (Hf t rv rt).
      + rew_list; subst; auto.
      + xchange SLL_part_fold_last_cons.
        xapp (IH (len + 1)).
        * apply upto_intro; subst; rew_list; math.
        * subst; rew_list; math.
        * subst; rew_list; auto.
        * xsimpl*.
  }
  xchange SSL_part_intro_empty.
  xapp (H); rew_list; auto.
  xvals*.
Qed.
Arguments sll_iter_spec {A} {EA} f ls Hf : rename.

Lemma sll_iter_drain_spec :
  forall A `{EA: Enc A}
         (f: func) (l: sll A) (I: list A -> hprop) (ls: list A),
         (forall t v r,
             ls = t & v ++ r ->
             SPEC (f v)
             PRE (I t)
             POSTUNIT (I (t & v))
         ) ->
         SPEC (sll_iter_drain f l)
         PRE (l ~> SLL ls \* I nil)
         POSTUNIT (I ls).
Proof.
  intros A EA f l I ls Hf.
  xcf.
  xlet as;=> aux Haux.
  assert (forall (t r : list A),
             ls = t ++ r ->
             SPEC (aux tt)
             PRE (I t \* l ~> SLL r)
             POSTUNIT (I ls)
         ). {
    intro t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r Hlstr.
    apply Haux; clear Haux.
    case_eq r; [intro Hnil | intros rv rt Heqr].
    - xchange SLL_nil. 
      xapp.
      xmatch.
      xvals*. { rewrite Hlstr, Hnil; rew_list; xsimpl*. }
    - xchange SLL_cons. intros tl.
      xapp.
      xmatch.
      xapp (Hf t rv rt).
      + rew_list; rewrite Hlstr, Heqr; auto.
      + case_eq rt; [intros Hrtnil | intros rth rtt Hrt].
        * xchange SLL_nil.
          xapp.
          xapp.
          do 2 xchange (@SLL_fold_nil A EA).
          xapp (IH (len + 1)).
          ** apply upto_intro; subst; rew_list; math.
          ** subst; rew_list; math.
          ** subst; rew_list; auto.
          ** xchange SLL_nil; xsimpl*.
        * xchange SLL_cons;=> rht_tl.
          xapp.
          xapp.
          xchange (SLL_fold_cons rth rtt rht_tl l).
          rewrite repr_eq. xpull;=> x_lt.
          xchange SLL_fold_cons.
          xapp (IH (len + 1)).
          ** apply upto_intro; subst; rew_list; math.
          ** subst; rew_list; math.
          ** subst; rew_list; auto.
          ** xsimpl*.
  }
  xapp (H); rew_list; auto.
  xsimpl*.
Qed.
Arguments sll_iter_drain_spec {A} {EA} f l I ls Hf : rename.
#[export] Hint Extern 1 (RegisterSpec sll_iter_drain) => Provide sll_iter_drain_spec.

Lemma sll_fold_spec :
  forall A `{EA: Enc A} B `{EB: Enc B} (f: func) (init: B) (l: sll A)
         (I: list A -> B -> hprop)  (ls: list A),
         (forall acc t v r,
             ls = t & v ++ r ->
             SPEC (f v acc)
             PRE (I t acc)
             POST (fun (acc: B) => I (t & v) acc)
         ) ->
         SPEC (sll_fold f init l)
         PRE (l ~> SLL ls \* I nil init)
         POST (fun (acc: B) => I ls acc \* l ~> SLL ls).
Proof.
  intros A EA B EB f init l I ls Hf.
  xcf.
  xlet as;=> aux Haux.
  assert (forall (acc: B) (t r : list A) (node: sll A),
             ls = t ++ r ->
             SPEC (aux node acc)
             PRE (I t acc \* node ~> SLL r \* l ~> SLL_part t node)
             POST (fun (acc: B) => I ls acc \* l ~> SLL ls)
         ). {
    intros acc t; remember (length t) as len; gen t acc.
    induction_wf IH: (upto (length ls)) len; intros t Hlen acc r node Hlstr.
    apply Haux; clear Haux.
    case_eq r; [intro Hnil | intros rv rt Heqr].
    - xchange SLL_nil. 
      xapp.
      xmatch.
      xvals*. { subst; rew_list; xsimpl*. xchange SLL_part_fold_last; xsimpl*. }
    - xchange SLL_cons. intros tl.
      xapp.
      xmatch.
      xapp (Hf acc t rv rt). { rew_list; subst; auto. }
      intros new_acc.
      xchange SLL_part_fold_last_cons.
      xapp (IH (len + 1)); try (apply upto_intro); try (subst; rew_list); try math; auto.
      intros res.
      xsimpl*.
  }
  xchange SSL_part_intro_empty.
  xapp (H); rew_list; auto.
  intros res.
  xsimpl*.
Qed.
Arguments sll_fold_spec {A} {EA} {B} {EB} f init l I ls Hf.
#[export] Hint Extern 1 (RegisterSpec sll_fold) => Provide sll_fold_spec.

Lemma sll_reverse_spec :
  forall A `{EA: Enc A} (l: sll A) (ls: list A),
         SPEC (sll_reverse l)
         PRE (l ~> @SLL A EA ls)
         POSTUNIT (l ~> @SLL A EA (rev ls)).
Proof.
  intros A EA l ls.
  xcf; auto.
  xlet as;=> loop Hloop.
  assert (forall (t r : list A) (node: sll A),
             ls = t ++ r ->
             SPEC (loop node)
             PRE (node ~> SLL r)
             POST (fun (lst: sll A) =>
                     node ~> SLL_part (rev r) lst \* lst ~> SLL (@nil A))
         ).  {
    intro t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r node Hlstr.
    apply Hloop; clear Hloop.
    case_eq r; [ intro Hrnil | intros rh rt Hreq ].
    - xchange SLL_nil.
      xapp.
      xmatch.
      xvals.
      rew_list; simpl SLL_part; rewrite repr_eq; xsimpl*.
    - xchange SLL_cons;=> tl.
      xapp.
      xmatch.
      xapp (IH (len + 1)). { try apply upto_intro; subst; rew_list; math. }
      { instantiate (1 := t & rh); rew_list; math. }
      { subst; rew_list; auto. }
      intros res.
      xapp;=> new_tl.
      xchange SLL_nil.
      xapp.
      case_eq (rev rt); [intros H_rt_nil | intros rev_rt_hd rev_rt_tl Hrevrt].
      + xchange SLL_part_nil; intros ->.
        xapp.
        xapp.
        xval.
        rewrite rev_cons, H_rt_nil; rew_list.
        simpl SLL_part; rewrite (repr_eq (fun _ => \exists _, _)).
        xsimpl.
        rewrite (repr_eq (fun _ => \[ _ ])).
        xsimpl*.
      + xchange SLL_part_cons;=> real_lst.
        xapp.
        xapp.
        xchange SLL_part_fold_last_cons.
        xval.
        rewrite rev_cons, Hrevrt; rew_list.
        simpl SLL_part; rewrite (repr_eq (fun _ => \exists _, _)).
        xsimpl.
  }
  xapp (H nil ls l); rew_list; auto.
  intro res.
  xmatch.
  xvals*.
  xchange SLL_nil.
  xchange SLL_part_fold_last.
  xsimpl*.
Qed.
#[export] Hint Extern 1 (RegisterSpec sll_reverse) => Provide sll_reverse_spec.


Lemma SLL_haffine {A: Type} `{EA: Enc A} (s: sll A) (ls: list A):
  haffine (s ~> SLL ls).
Proof.
  gen s; induction ls as [| hd tl]; intro s.
  rewrite SLL_nil; auto.
  apply haffine_Ref.
  rewrite SLL_cons; auto.
  apply haffine_hexists; unfold haffine_post;=> tl'.
  apply haffine_hstar; auto.
  apply haffine_Ref.
Qed.

