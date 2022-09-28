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
