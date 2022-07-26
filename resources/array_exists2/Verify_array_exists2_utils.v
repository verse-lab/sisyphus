Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayExists2 Require Import Common_ml.

Lemma neq_drop_list : forall A `{EA: Enc A} `{IA: Inhab A} (i: int) (l: list A) (x: A) (l': list A),
    0 <= i < LibListZ.length l -> l = x :: l' ->
    drop (i + 1) l <> l.
Proof using.
  introv _ _ Hi Hl.
  rewrite <- (@list_eq_take_app_drop A (i + 1) l) at 2; try math.
  rewrite <- app_nil_l  at 1.
  intros contra.
  apply app_cancel_r  in contra.
  rewrite Hl in contra.
  rewrite take_cons in contra; (math || auto). discriminate contra.
Qed.

Lemma take_read_app : forall A `{EA: Enc A} `{IA: Inhab A} (l: list A) (i: int),
    0 <= i < LibListZ.length l ->
    l = take i l & l[i] ++ drop (i + 1) l.
Proof.
  intros. math_rewrite (i = i + 1 - 1). math_rewrite (i + 1 - 1 + 1 = i + 1).
  rewrite <- take_pos_last; auto.
  rewrite list_eq_take_app_drop; auto. math.
Qed.

Lemma drop_cons' : forall A `{EA: Enc A} `(IA: Inhab A) (x : A) (l : list A) (i : credits),
    0 <= i < LibListZ.length l ->
    drop i l  = l[i] :: drop (i + 1) l.
Proof using.
  intros. gen i. induction l; intros.
  + rew_list in H. math.
  + pose proof (Z.eqb_spec i 0) as Hr.
    inversion Hr.
    ++ rewrite H1, drop_zero, drop_cons; try math. rew_list. rewrite drop_zero; auto.
    ++ rewrite !drop_cons_pos; try math. math_rewrite ( i + 1 - 1 = i). rewrite IHl.
       +++ rewrite read_cons_pos; try math. math_rewrite (i - 1 + 1 = i); auto.
       +++ split; try math. rew_list in H. math.
Qed.

Lemma length_nonzero_cons A (l: list A) :
 0 < LibListZ.length l -> exists x l', x :: l' = l.
Proof using. intros. case_eq l.
             + intros ->. rewrite LibListZ.length_nil in H. math.
             + intros. exists a l0; auto.
Qed.

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
