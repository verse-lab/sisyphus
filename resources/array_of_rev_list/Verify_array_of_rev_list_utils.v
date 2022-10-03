Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Common_ml.

Lemma for_downto_spec : forall (from: int) (down_to: int) (f: func),
  forall (I: int -> hprop),
    (from >= down_to - 1) ->
    (forall i, down_to <= i <= from ->
     SPEC (f i)
     PRE (I i)
     POST (fun (_: unit) => I (i - 1))) ->
  SPEC (for_downto from down_to f)
    PRE (I from)
    POST (fun (_: unit) => I (down_to - 1)).
Proof using.
  intros from down_to.
  induction_wf IH: (downto down_to) from.
  intros f I Hvld HI.
  xcf. 
  xif.
  - rewrite Px0__, istrue_isTrue_eq; intros ->.  
    xapp (HI down_to); try math.
    xsimpl*.
  - rewrite Px0__, istrue_isTrue_eq; intros Hneq.
    xif; try math.
    + intros Hgt.
      xapp (HI from); try math.
      xapp (IH (from - 1)); try (apply downto_intro; try math); try math; auto.
      * intros i Hi; apply HI; math.
      * xsimpl*.
    + intros Hgt.
      assert (H: from = down_to - 1) by math.
      rewrite H.
      xvals*.
Qed.
Arguments for_downto_spec from down_to f I Hf HI : rename, clear implicits.

Lemma hd_spec: forall (A: Type) `{EA: Enc A} `{IA: Inhab A} (ls: list A),
    length ls > 0 ->
    SPEC_PURE (hd ls)
      POST (fun (a: A) => \[a = ls[0]]).
Proof.
  intros A EA IA ls Hls.
  xcf.
  xmatch.
  - rew_list in Hls; math.
  - xvals. rew_list; auto.
Qed.    

Lemma tl_spec: forall (A: Type) `{EA: Enc A} (ls: list A),
    length ls > 0 ->
    SPEC_PURE (tl ls)
      POST (fun (ls': list A) => \[ls' = drop 1 ls]).
Proof.
  intros A EA ls Hls.
  xcf.
  xmatch.
  - rew_list in Hls; math.
  - xvals. rew_list; auto.
Qed.    

Lemma read_rev_helper (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  0 <= i < length l ->
  l[i] = (rev l)[length l - i - 1].
Proof.
  gen i; induction l as [| l ls IHls].
  + intros i; rewrite length_nil; math.
  + intros i; rewrite length_cons; intros Hi.
    case (Z.eqb_spec i 0); intros Hi_zero.
    * rewrite Hi_zero, rev_cons, read_zero, read_last_case, If_l; auto; rewrite length_rev; math.
    * rewrite read_cons_pos, rev_cons, read_last_case, If_r; try rewrite length_rev; try math.
      rewrite IHls; try math.
      f_equal; math.
Qed.      

Lemma read_rev (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  0 <= i < length l ->
  (rev l)[i] = l[length l - i - 1].
Proof.
  intros Hvld.
  rewrite (read_rev_helper l); try math.
  f_equal.
  math.
Qed.

Lemma list_iter_spec : forall [A : Type] {EA : Enc A}
                              (f : func) (l : list A)
                              (I : list A -> hprop),
    (forall (x : A) (t r : list A), l = t ++ x :: r -> SPEC (f x)
                                                         PRE I t
                                                         POSTUNIT I (t & x)) ->
SPEC (List_ml.iter f l)
PRE I nil
POSTUNIT I l.
Proof using.
  intros A EA f l I HI.
  apply List_proof.iter_spec; auto.
Qed.
Arguments list_iter_spec {A} {EA} f l I HI : rename.


Lemma list_iteri_aux_spec : forall A `{EA: Enc A},
  forall (f:func) (i: int) (r t l: list A) (I: list A -> hprop)  ,
    (forall i x t r, (l = t ++ x :: r) -> i = length t ->
                     SPEC (f i x) 
                       PRE (I t) 
                       POST (fun (unused: unit) => I (t & x))) ->  
    l = t ++ r ->
    i = length t ->
    SPEC (list_iteri_aux f i r)
      PRE (I t)
      POST (fun (unused: unit) => I l).
Proof using.
  introv Hf. gen r t. induction_wf IH: (upto (length l)) i.
  intros r t Hl Hi.
  xcf.
  xmatch.
  - xvals.
    rew_list in Hl; rewrite Hl; xsimpl.
  - xapp (Hf i h t t0); auto.
    xapp; try xsimpl; rew_list; try apply upto_intro; try math.
    rewrite Hl; rew_list; math.
    auto.
Qed.

Lemma list_iteri_spec : forall A `{EA: Enc A},
  forall (f:func)  (l: list A) (I: list A -> hprop)  ,
    (forall i x t r, (l = t ++ x :: r) -> i = length t ->
     SPEC (f i x) 
     PRE (I t) 
     POST (fun (unused: unit) => I (t & x))) ->  
  SPEC (list_iteri f l)
    PRE (I nil)
    POSTUNIT (I l).
Proof using.
  =>> Hf; xcf.
  xapp (@list_iteri_aux_spec _ _ f 0  l); auto; try xsimpl; rew_list; try math.
  auto.
Qed.
Arguments list_iteri_spec {A} {HA} f s l I Hf : rename.

Lemma list_ml_iteri_spec : forall A `{EA: Enc A},
  forall (f:func)  (l: list A) (I: list A -> hprop)  ,
    (forall i x t r, (l = t ++ x :: r) -> i = length t ->
     SPEC (f i x) 
     PRE (I t) 
     POST (fun (unused: unit) => I (t & x))) ->  
  SPEC (List_ml.iteri f l)
    PRE (I nil)
    POST (fun (unused: unit) => I l).
Proof using.
  =>> Hf; xcf.
  xlet as;=> tmp Htmp.

  assert (tmp_spec:
  forall  (i: int) (r t: list A),
    l = t ++ r ->
    i = length t ->
    SPEC (tmp i r)
      PRE (I t)
      POSTUNIT (I l)). {
    introv Hl0 Hlen.
    gen r t. induction_wf IH: (upto (length l)) i.
    intros r t Hl Hi.
    apply Htmp; clear Htmp.
    xmatch.
    - xvals.
      rew_list in Hl; rewrite Hl; xsimpl.
    - xapp (Hf i a t l1); auto.
      xapp; try xsimpl; rew_list; try apply upto_intro; try math.
      rewrite Hl; rew_list; math.
      auto.
  }
  xapp (tmp_spec 0 l); auto; try xsimpl; rew_list; try math.
Qed.
Arguments list_ml_iteri_spec {A} {HA} f s l I Hf : rename.


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

Tactic Notation "xref"
       simple_intropattern(r) :=
    xapp; intros r.

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

Tactic Notation "xunit" :=
  xmatch; [xapp || xval].

Definition eq_ind_reduce :
  forall [A : Type] (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P x :=
  fun (A: Type) => fun (x: A) (P: A -> Prop) =>
    fun (Hp: P x) (y: A) => fun (Heq: x = y) => Hp.
