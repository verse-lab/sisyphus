Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Sseq_ml.
From Common Require Import Utils Solver.
From Common Require Import Tactics.

(** Lazy values: a lazy value of type [a] is represented at type [unit->'a].
    [Lazyval P f] asserts that [f] is a lazy value whose evaluation produces
    a value satisfying the (pure) predicate [P]. *)

Definition Lazyval A `{EA:Enc A} (P:A->Prop) (f:val) : Prop :=
  SPEC_PURE (f tt) POST (fun a => \[P a]).

Definition LSeq_node A `{EA:Enc A} (LSeq: list A -> t_ A -> Prop) (L:list A) (s: node_ A) : Prop :=
 match L with
 | nil => s = Nil
 | x::L' => exists f', s = Cons x f' /\ LSeq L' f'
 end.

Lemma LSeq_node_Nil : forall A (EA:Enc A) (LSeq: list A -> t_ A -> Prop),
  LSeq_node LSeq (@nil A) Nil.
Proof using. intros. simpl. auto. Qed.

Lemma LSeq_node_Cons : forall A (EA: Enc A) (LSeq: list A -> t_ A-> Prop) (x: A) (L': list A) (f: func),
  LSeq L' f ->
  LSeq_node LSeq (x::L') (Cons x f).
Proof using. introv Hf. simpl. exists* f. Qed.

Fixpoint LSeq A `{EA: Enc A} (L: list A) (f: t_ A) : Prop :=
  Lazyval (LSeq_node (@LSeq A EA) L) f.

Lemma LSeq_intro : forall A `{EA:Enc A} (L:list A) (f: t_ A),
  SPEC_PURE (f tt) POST (fun a => \[(LSeq_node (@LSeq A EA) L) a]) ->
  LSeq L f.
Proof using.
  (* Coq forces us to do a case analysis on L in order to unfold the fixpoint definition. *)
  intros. unfold LSeq, Lazyval. destruct L; simpl; xapplys* H.
Qed.

Lemma LSeq_if : forall A `{EA:Enc A} (L:list A) (f: t_ A),
    LSeq L f ->
    (SPEC_PURE (f tt) POST (fun a => \[(LSeq_node (@LSeq A EA) L) a])) .
Proof using.
  intros A EA L; case L as [| hd tl]; intros f; simpl; auto.
Qed.

Lemma fold_spec : forall `{A: Type} `{Enc A} `{B: Type} `{Enc B} (f: val) (init : B) (s: t_ A) (ls: list A) (fp: B -> A -> B),
    (forall acc v,
        SPEC_PURE (f acc v)
                  POST \[= fp acc v]) ->
      SPEC (fold f init s)
           PRE \[LSeq ls s]
           POST \[= List.fold_left fp ls init].
Proof using.
  introv Hspec. gen init s. induction ls; xcf.
  { xpull ;=> HLseq. apply LSeq_if in HLseq. xapp. xmatch. xvals. auto. }
  { xpull ;=> HLseq. apply LSeq_if in HLseq. xapp ;=> nxt'. simpl LSeq_node;=>[nxt [-> Hnxt]].
    xmatch. xapp. xapp; auto. xsimpl. auto. }
Qed.

Arguments fold_spec {A} {HA} {B} {HB} f init s ls fp _ _ _ _ : rename.

Lemma length_spec : forall A `{Enc A} s (ls: list A),
  SPEC (length'__ s)
    PRE \[LSeq ls s]
    POST (fun len => \[ len = length ls ]).
Proof using.
  xcf; auto.
  xlet (fun f => forall (acc: int) (v: A), SPEC_PURE (f acc v) POST \[= (acc + 1) ]) as; [ | intros f fSpec].
  { xvals; math. }
  xpull ;=> Hs.
  xapp (fold_spec f 0 s ls (fun (acc: int) _ => acc + 1) fSpec) ; auto.
  xsimpl.
  clear.
  cut (forall a, List.fold_left (fun (acc : credits) (_ : A) => acc + 1) ls a = a + length ls). {
    intros H.
    apply H.
  }
  induction ls.
  - intros a; simpl; rew_list; math.
  - intros a'; simpl; rewrite IHls; rew_list; math.
Qed.

Arguments length_spec {A} {HA} s ls : rename.
#[export] Hint Extern 1 (RegisterSpec length_spec) => Provide length_spec.


Lemma iteri_spec : forall A `{EA: Enc A},
  forall (f:func) (s: t_ A)  (l: list A) (I: list A -> hprop)  ,
  (forall x t r i, (l = t++x::r) -> i = length (t) ->
     SPEC (f i x) PRE (I t) POSTUNIT (I (t&x))) ->
  SPEC (iteri f s)
    PRE (\[@LSeq A EA l s] \* I nil)
    POSTUNIT (I l).
Proof using.
  =>> M. xcf; auto.
  xlet.
  asserts aux_spec: (
   forall i r t s,
     l = t ++ r ->
     i = length t ->
     SPEC (aux f s i)
     PRE (I t \* \[LSeq r s])
     POSTUNIT (I l)
                    ).
  {
    intro i; induction_wf IH: (upto (length l)) i.
    intros r t s' Hl Hi.
    eapply Spec_aux; clear Spec_aux.
    xpull ;=> HLseq. apply LSeq_if in HLseq.
    case_eq r.
    * intros ->. xapp. xmatch. xvals. rewrite app_nil_r in Hl; rewrite Hl; xsimpl.
    * intros x xs ->. xapp;=>result [nxt_r [-> Hnxt_r]].
      xmatch. xseq. xapp~ (M x t xs).
      xapp.
      ** unfold upto. split; try math.
         rewrite Hl; rewrite length_app; rewrite Hi; rewrite length_cons.
         math.
      ** rewrite Hl. rewrite <- app_cons_r. auto.
      ** rewrite length_last. math.
      ** auto.
      ** xsimpl.
  }
  xpull;=> Hlseq.
  xapp (aux_spec 0 l); auto; try xsimpl.
Qed.
Arguments iteri_spec {A} {HA} f s l I Hf : rename.

Hint Extern 1 (RegisterSpec iteri) => Provide iteri_spec.


Ltac sis_seq_solver :=
  lazymatch goal with
  | [H: LSeq_node _ ?l Sseq_ml.Nil |- _] =>
      let lh := fresh "lh" in
      let lt := fresh "lt" in
      let e_v := fresh "e_v" in
      let H1 := fresh "H1" in
      let H2 := fresh "H2" in
      let H3 := fresh "H3" in
      destruct l as [| lh lt]; simpl in H;
      [auto| destruct H as [H1 [H2 H3]]; inversion H2]
  end.

