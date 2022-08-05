Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsListPartition Require Import Common_ml.

Fixpoint MList A `{EA:Enc A} (l:list A) (r:loc) : hprop :=
  match l with
  | nil => r ~~~> `{ hd' := (@None A); tl' := (@None (mut_list_ A))}
  | h :: l' =>  \exists q,  r ~~~> `{ hd' := Some h; tl' := Some q} \* (MList l' q)
  end.

Fixpoint MList_partial A `{EA:Enc A} (l:list A) (lst: loc) (r: loc): hprop :=
  match l with
  | nil => r ~> MList (@nil A) \* \[r = lst]
  | h :: nil => lst ~> MList (h :: nil) \* \[r = lst]
  | h :: l' =>  \exists q,  r ~~~> `{ hd' := Some h; tl' := Some q} \* (MList_partial l' lst q)
  end.

Lemma MList_partial_is_MList : forall A `{EA: Enc A} (l: list A) (r: loc),
    r ~> MList l = \exists lst, r ~> MList_partial l lst.
Proof.
  intros. gen r. induction l.
  + intros r. simpl. rewrite !repr_eq. apply himpl_antisym.
    ++ xsimpl*. rewrite repr_eq. xsimpl*.
    ++ xsimpl*. intros q. rewrite !repr_eq.  xsimpl*.
  + intros r. gen IHl. case l; [intros IHl | intros x l' IHl].
    ++ simpl. rewrite !repr_eq. apply himpl_antisym; xpull. intros. xsimpl*. rewrite !repr_eq. xsimpl*.
       instantiate (1:= x). xsimpl*.
       intros. rewrite !repr_eq. xsimpl*. intros.  rewrite H. auto.
    ++ intros.
       asserts Hun : (r ~> MList (a :: x :: l') = \exists q, r ~~~> `{ hd' := Some a; tl' := Some q} \* q ~> MList (x :: l')). {
         simpl. auto.
       }
       rewrite Hun; clear Hun.
       apply himpl_antisym; xpull; intros.
    *  rewrite IHl. xsimpl*. intros. instantiate (1:= x1). simpl. rewrite !repr_eq. xsimpl*.
    * asserts Hun : (r ~> MList_partial (a :: x :: l') x0 = \exists q, r ~~~> `{ hd' := Some a; tl' := Some q} \* q ~> MList_partial (x :: l') x0). {
         simpl. auto.
      }
      rewrite Hun; clear Hun. xpull. intros q. xsimpl*. rewrite IHl. xsimpl*.
Qed.


Definition MList_internal A `{EA: Enc A} (l: list A) (r: loc) : hprop :=
  \exists q: option loc,
      match q with
      | None => MList l r
      | Some q => q ~> MList l \* r ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := Some q}
      end.

Definition MList_internal_partial A `{EA: Enc A} (l: list A) (lst: loc) (r: loc) : hprop :=
  \exists q: option loc,
      match q with
      | None => r ~> MList_partial l lst
      | Some q => q ~> MList_partial l lst \* r ~~~> `{ Common_ml.hd' := (@None A); Common_ml.tl' := Some q}
      end.

Lemma MList_eq : forall r A `{EA: Enc A} (h: A) (l: list A),
    (r ~> MList (h :: l)) =
     \exists q,  r ~~~> `{ hd' := Some h; tl' := Some q} \* (MList l q).
Proof using. auto. Qed.

Lemma MList_eq_nil : forall r A `{EA: Enc A},
    (r ~> MList (@nil A)) =
      r ~~~> `{ hd' := (@None A); tl' := (@None (mut_list_ A))}.
Proof using. auto. Qed.

Tactic Notation "xopen" constr(r) :=
  xchange (MList_eq r); xpull.

Tactic Notation "xclose" constr(r) :=
  xchange <- (MList_eq r).

Tactic Notation "xclose" "*" constr(r) :=
  xclose r; auto_star.

Lemma dummy_spec : forall A `{EA: Enc A},
    SPEC_PURE (dummy tt)
              POST (fun r => r ~> MList (@nil A)).
Proof using. intros. xcf. xapp. intros r.  rewrite MList_eq_nil. xsimpl*. Qed.

Hint Extern 1 (RegisterSpec dummy) => Provide dummy_spec.


Lemma create_spec : forall A `{EA: Enc A} (x: A),
    SPEC_PURE (create x)
              POST (fun r => r ~> MList (x :: nil)).
Proof using. intros. xcf. xapp. intros q.  xapp. intros r.  rewrite MList_eq. xsimpl*. Qed.

Hint Extern 1 (RegisterSpec create) => Provide create_spec.



(** NOTE: The following is copied from resources/seq_to_array.
    TODO: Figure out a better build hierarchy to avoid copying tactics
 *)

Ltac sep_solve_int := lazymatch goal with
  | [|- forall Y, ?X] => let y := fresh in intros y; sep_solve_int
  | [|- Triple ?Code ?Pre ?Post ] => xgo*
  | [|- himpl ?X ?Y ] => xgo*
  | [ H: ?X = ?Z |- ?X = ?Y ] => autorewrite with sep_solve_db; auto
  | _ => idtac
  end.
Ltac sep_solve := repeat progress (auto; sep_solve_int).

#[export] Hint Rewrite nil_eq_rev_inv: sep_solve_db.

Ltac done := auto; tryif only 1 : idtac then fail else idtac.
Tactic Notation "by" tactic(t) := t; done.
Tactic Notation "first" tactic(t) := only 1 : t.

Tactic Notation "xdestruct" := xmatch Xcase_as.
Tactic Notation "xdestruct" simple_intropattern(p1) := xmatch Xcase_as; intros p1.
Tactic Notation "xdestruct"
       simple_intropattern(p1)
       simple_intropattern(p2):= xmatch Xcase_as; intros p1 p2.
Tactic Notation "xdestruct"
       simple_intropattern(p1)
       simple_intropattern(p2)
       simple_intropattern(p3)
  := xmatch Xcase_as; intros p1 p2 p3.
Tactic Notation "sep_split_tuple"
       hyp(H)
       simple_intropattern(p1)
       simple_intropattern(p2) :=
  inversion H as [[p1 p2]].
Tactic Notation "xalloc"
       simple_intropattern(arr)
       simple_intropattern(data)
       simple_intropattern(Hdata) :=
    xapp; try math; intros arr data Hdata.

Tactic Notation "xpurefun"
  simple_intropattern(f)
  simple_intropattern(Hf) "using"
  constr(fn) :=
    xlet fn as; (first by sep_solve); intros f Hf.

Tactic Notation "xalloc"
       simple_intropattern(arr)
       simple_intropattern(data)
       simple_intropattern(Hdata) :=
    xapp; try math; intros arr data Hdata.

Tactic Notation "xpullpure"
       simple_intropattern(H1) :=
  xpull; intro H1.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
  :=
  xpull; intros H1 H2.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
  :=
  xpull; intros H1 H2 H3.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
       simple_intropattern(H4)
  :=
  xpull; intros H1 H2 H3 H4.
Tactic Notation "xpullpure"
       simple_intropattern(H1)
       simple_intropattern(H2)
       simple_intropattern(H3)
       simple_intropattern(H4)
       simple_intropattern(H5)
  :=
  xpull; intros H1 H2 H3 H4 H5.

Tactic Notation "xmatch_case_0"  :=
  xmatch Xcase_as.
Tactic Notation "xmatch_case_0" "with"
       simple_intropattern(h1)
  :=
  xmatch Xcase_as; intros h1.
Tactic Notation "xmatch_case_0" "with"
       simple_intropattern(h1)
       simple_intropattern(h2) :=
  xmatch Xcase_as; intros h1 h2.

Tactic Notation "xmatch_case_1"  :=
  xmatch Xcase_as; (first sep_solve); intros _.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
       simple_intropattern(h3)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2 h3.
Tactic Notation "xmatch_case_1" "with"
       simple_intropattern(h1)
       simple_intropattern(h2)
       simple_intropattern(h3)
       simple_intropattern(h4)
  :=
  xmatch Xcase_as; (first sep_solve); intros _ h1 h2 h3 h4.

Tactic Notation "xletopaque"
       simple_intropattern(idx)
       simple_intropattern(Hidx) :=
  xlet as;=> idx Hidx.

Tactic Notation "xvalemptyarr" :=
  xapp; xsimpl.
