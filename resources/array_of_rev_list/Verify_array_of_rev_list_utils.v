Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Common_ml.

Lemma drop_nth : forall A l v r i (xs: list A),
    xs = l ++ v :: r ->
    i = length l ->
    drop i xs = v :: drop (i + 1) xs.
Proof.
  intros A l v r i xs -> ->.
  rewrite drop_app_length.
  rewrite app_cons_r.
  assert ((length l + 1) = length (l & v)) as H by (rewrite length_last; math).
  rewrite H.
  rewrite drop_app_length.
  auto.
Qed.

Lemma hd_spec : forall A `{EA:Enc A} (l l':list A) (hd : A),
   hd :: l' = l ->
  SPEC_PURE (Common_ml.hd l)
    POST (fun x => \[x = hd]).
Proof using.
  xcf.
  rewrite <- H.
  xmatch.
  xvals. auto.
Qed.

Lemma tl_spec : forall A `{EA:Enc A} (l l':list A) (hd : A),
   hd :: l' = l ->
  SPEC_PURE (Common_ml.tl l)
    POST (fun x => \[x = l']).
Proof using.
  xcf.
  rewrite <- H.
  xmatch.
  xvals. auto.
Qed.

Lemma drop_cons : forall (A: Type) (l : list A) (i : credits),
    0 <= i <= (length l - 2) ->
    (length l) > (length l) - (i + 1).
Proof.
  intros.
  try math.
Qed.

Lemma drop_cons_two : forall (A: Type) (l : list A) (i : credits),
    0 <= i < length l ->
    exists hd r,
      drop i l = hd :: r.
Proof.
  intros. gen i.
  induction l as [ | x l' IHl']; intros.
  - rew_list in H.
    math.
  - rew_list in H.
    case (0 <? i) eqn: Hi.
    -- pose proof (Z.ltb_spec0 0 i).
       inversion H0.
       --- rewrite drop_cons_pos; try math.
           apply IHl'. math.
       --- rewrite Hi in H1. discriminate.
    -- pose proof (Z.ltb_spec0 0 i).
       inversion H0.
       --- rewrite Hi in H1. discriminate.
       --- assert (i <= 0). { try math. }
           assert (i = 0). { math. }
           rewrite H4.
           rewrite drop_zero.
           eauto.
Qed.

Lemma iteri_spec : forall A `{EA:Enc A} (l:list A) (f:func),
  forall (I:list A -> hprop),
  (forall x t r i, (l = t++x::r) -> i = length t ->
     SPEC (f i x) PRE (I t) POSTUNIT (I (t&x))) ->
  SPEC (List_ml.iteri f l)
    PRE (I nil)
    POSTUNIT (I l).
Proof using.
Admitted.


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
