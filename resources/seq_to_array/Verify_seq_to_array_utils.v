Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Common_ml.

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

Lemma list_fold_spec : forall A `{EA: Enc A} B `{EB: Enc B}
                              (f: func) (init: B) (l: list A),
  forall (I: list A -> B -> hprop),
  (forall acc v t r, (l = t++v::r) ->
     SPEC (f acc v)
     PRE (I t acc)
     POST (fun acc => I (t&v) acc)) ->
  SPEC (List_ml.fold_left f init l)
    PRE (I nil init)
    POST (fun acc => I l acc).
Proof using.
  intros A EA B EB f init l I f_spec. gen init.
  cuts G: (forall r t init,
              l = t ++ r ->
              SPEC (List_ml.fold_left f init r)
              PRE I t init
              POST (fun acc : B => I l acc)).
  { intros init; applys~ (G l nil init). }
  intros r. induction_wf IH: list_sub r.
  intros t init Ht. xcf.
  xmatch.
  - xvals.
    rewrite Ht. rewrite <- TEMP; rew_list; xsimpl.
  - xapp (f_spec init a t l1); auto. { rewrite Ht. rewrite TEMP. auto. }
    intros acc.
    xapp. rewrite <- TEMP. apply list_sub_cons. { rew_list; try rewrite TEMP; auto. }
    xsimpl.
Qed.
Arguments list_fold_spec {A} {HA} {B} {HB} f init l I Hf : rename.

Lemma list_fold_length_rev : forall A (xs : list A), 
    List.fold_left
         (fun '((i,acc) : credits * list A) (x : A) => (i + 1, x :: acc)) xs (0, nil) =
      (length xs, rev xs).
Proof.
  intros A.
  cuts G: (forall (xs : list A)  (i: int) (init: list A),
          List.fold_left
            (fun '((i,acc) : credits * list A) (x : A) =>
               (i + 1, x :: acc))
            xs (i, init) = (i + length xs, rev xs ++ init)). {
    intros xs; rewrite G. f_equal; rew_list; auto.
  }
  intros xs; induction xs as [| x xs IHxs]; simpl.
  - intros i init; rew_list; f_equal; auto; math.
  - intros i init; simpl.
    rewrite IHxs.
    rewrite !length_cons.
    f_equal; try math. rew_list; auto.
Qed.

Lemma drop_last: forall A (xs rst: list A) (lst: A),
    rev xs = lst :: rst ->
    drop (length xs - 1) xs = lst :: nil.
Proof.
  intros A xs. induction_wf IH: list_sub xs.
  case_eq xs.
  - intros Hxs rst lst; rewrite rev_nil; intros H; inversion H.
  - intros hd tl Hxs; intros rst lst Hlst; rewrite length_cons.
    math_rewrite ((1 + length tl - 1) = length tl).
    case_eq tl.
    * intros Htl. rewrite Htl in *. rewrite rev_cons in Hlst.
      rewrite last_nil in Hlst.
      rewrite length_nil; rewrite drop_zero.
      f_equal. inversion Hlst; auto.
    * intros y ys Hys; rewrite length_cons.
      math_rewrite (1 + length ys = length ys + 1).
      rewrite drop_cons; try math.
      asserts Hlen: ((length ys) = length (y :: ys) - 1). {
        rewrite length_cons; math.
      } rewrite Hlen; clear Hlen.
      rewrite <- Hys.
      rewrite rev_cons in Hlst.
      rewrite <- (app_cons_one_r lst) in Hlst.
      assert (lst :: nil = nil & lst) by  (rew_list; auto).
      rewrite H in Hlst.
      assert (Hlst' := Hlst).
      apply last_eq_middle_inv in Hlst.
      case Hlst; clear Hlst.
      ** intros [Htl [Hlsthd Hrd] ].
         (* B109 *)
         apply rev_eq_nil_inv in Htl.
         rewrite Htl in Hys; inversion Hys.
      ** intros [rst_but_last Hrst].
         eapply (IH tl _ rst_but_last lst).
         rewrite Hrst in Hlst'.
         rewrite <- last_app in Hlst'.
         apply last_eq_last_inv in Hlst'.
         case Hlst' as [H1 H2].
         rewrite H1.
         rewrite app_last_l.
         rewrite app_nil_l.
         auto.
         Unshelve.
         rewrite Hxs. apply list_sub_cons.
Qed.    

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

Lemma case_rev_split : forall A (xs: list A) v l r,
    rev xs = l ++ v :: r ->
    xs = rev r ++ v :: rev l.
Proof.
  intros A xs; induction xs.
  - intros v l r; rewrite rev_nil; intros Hnil.
    apply nil_eq_app_inv in Hnil. case Hnil as [H1 H2].
    inversion H2.
  - intros v l r. 
    intros Hr; assert (Hr' := Hr).
    rewrite rev_cons in Hr. rewrite (app_cons_r v) in Hr.
    apply last_eq_middle_inv in Hr.
    case Hr.
    * intros [Hrevls [Ha Hnil]].
      rewrite Hnil. rewrite rev_nil.
      rewrite app_nil_l. rewrite Ha.
      apply f_equal.
      rewrite <- Hrevls.
      rewrite rev_rev.
      auto.
    * intros [pre Hrpre].
      rewrite Hrpre in Hr'.
      rewrite rev_cons in Hr'.
      rewrite <- last_cons in Hr'.
      rewrite <- last_app in Hr'.
      apply last_eq_last_inv in Hr'.
      case Hr' as [H1 H2].
      rewrite (IHxs _ _ _ H1).
      rewrite Hrpre.
      rewrite rev_last.
      rew_list.
      auto.
Qed.      

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
