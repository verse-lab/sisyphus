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

Lemma SLL_cons A `{EA: Enc A} (a: sll A) (h: A) (t : list A):
  a ~> SLL (h :: t) = \exists (lt: loc), a ~~> Node h lt \* lt ~> SLL t.
Proof. simpl SLL; rewrite repr_eq; xsimpl*. Qed.

Lemma SLL_part_nil A `{EA: Enc A} (a: sll A) (rst: sll A):
  a ~> SLL_part (@nil A) rst = \[a = rst].
Proof. simpl SLL_part; rewrite repr_eq; xsimpl*. Qed.

Lemma SLL_part_cons A `{EA: Enc A} (a: sll A) (h: A) (t : list A) (rst: sll A):
  a ~> SLL (h :: t) = \exists (lt: loc), a ~~> Node h lt \* lt ~> SLL t.
Proof. simpl SLL; rewrite repr_eq; xsimpl*. Qed.

Lemma SLL_part_unfold_last A `{EA: Enc A} (t: list A) (a: sll A) (lst: sll A):
  a ~> SLL_part t lst \* lst ~~> @Nil A ==>
    a ~> SLL t.
Proof.
  gen a lst; induction t as [| hd tl]; intros a lst.
  - simpl SLL_part; simpl SLL; rewrite !repr_eq.
    xsimpl*; intros ->; xsimpl*.
  - simpl SLL_part; simpl SLL; rewrite !repr_eq.
    xsimpl*;=> tl.
Qed.

Lemma SLL_part_unfold_last_cons A `{EA: Enc A} (t: list A) (a: sll A) (v: A)
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


Lemma sll_iter_spec :
  forall A `{EA: Enc A}
         (f: func) (l: sll A) 
         (ls: list A)
         (I: list A -> hprop),

         (forall t v r,
             ls = t & v ++ r ->
             SPEC (f v)
             PRE (I t)
             POSTUNIT (I (t & v))
         ) ->
         SPEC (sll_iter f l)
         PRE (I nil \* l ~> SLL ls)
         POSTUNIT (I ls \* l ~> SLL ls).
Proof.
  intros A EA f l ls I Hf.
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
      xvals*. { subst; rew_list; xsimpl*. xchange SLL_part_unfold_last. xsimpl*. }
    - xchange SLL_cons. intros tl.
      xapp.
      xmatch.
      xapp (Hf t rv rt).
      + rew_list; subst; auto.
      + xchange SLL_part_unfold_last_cons.
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
    
