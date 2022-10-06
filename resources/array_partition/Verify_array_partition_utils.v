Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayPartition Require Import Common_ml.

Lemma array_iter_spec :
  forall A `{EA: Enc A} (f: func) (a: array A) (l: list A),
  forall (I: list A -> hprop),
  (forall v (t r: list A),
      (l = t++v::r) ->
     SPEC (f v)
     PRE (I t)
     POST (fun (_: unit) => I (t&v))) ->
  SPEC (array_iter f a)
    PRE (a ~> Array l \* I nil)
    POST (fun (_: unit) => a ~> Array l \* I l).
Proof using.
  intros A EA f a l I f_spec.
  xcf.
  xapp.
  xlet as;=> loop Hloop.
  assert (Hloop_spec: forall i (t r: list A),
             l = t ++ r ->
             i = LibListZ.length t ->
             SPEC (loop i)
               PRE (I t \* a ~> Array l)
               POST (fun (_: unit) => I l  \* a ~> Array l)
         ). {
    intros i; induction_wf IH: (upto (LibListZ.length l)) i.
    intros t r Hl Hi; apply Hloop; clear Hloop.
    assert (Higt0: 0 <= i) by (rewrite Hi; apply length_nonneg).
    xif;=> Hivl.
    - assert (IA: Inhab A). {
        destruct l; [rew_list in Hivl; math |].
        exact (Inhab_of_val a0).
      }
      xapp; [apply int_index_prove; try math | ].
      assert (Hl_eq: l = t ++ l[i] :: drop 1 r). {
        rewrite Hl; repeat f_equal.
        rewrite read_app, If_r; try math; rewrite Hi, minus_self.
        apply (eq_of_extens IA).
        - rew_list;
          rewrite ?length_drop; try math;
          rewrite Hl in Hivl; rew_list in Hivl; math.
        - intros j. rewrite index_eq_index_length, int_index_eq.
          intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_drop; f_equal; try apply int_index_prove; math.
      }
      xapp (f_spec l[i] t (drop 1 r)); auto.
      xapp (IH (i + 1)).
      * apply upto_intro; try math.
      * rewrite app_last_l; apply Hl_eq.
      * rew_list; math.
      * xsimpl*.
    - xvals*. {
        cut (t = l). {
          intros ->; xsimpl*.
        }
        assert (HI: i >= LibListZ.length l) by math.
        rewrite Hl, Hi in HI; rew_list in HI.
        assert (LibListZ.length r = 0) by math.
        rewrite Hl, (length_zero_inv r); rew_list; auto.
      }
  }
  xapp (Hloop_spec (0) (nil) (l)); rew_list; auto.
  xsimpl*.
Qed.
Arguments array_iter_spec {A} {EA} f a l I Hf : rename.

Lemma array_take_spec :
  forall A `{EA: Enc A} (i: int) (a: array A) (l: list A), 0 <= i ->
  SPEC (array_take i a)
    PRE (a ~> Array l)
    POST (fun (arr: loc) => a ~> Array l \* arr ~> Array (take i l)).
Proof using.
  intros.
  xcf.
  xapp.
  xif;=> Hcond.
  - rewrite Px0__, istrue_isTrue_eq in Hcond; apply length_zero_inv in Hcond; rewrite Hcond, take_nil.
    xapp*;=> arr.
    xsimpl*.
  - rewrite Px0__, istrue_isTrue_eq in Hcond.
    assert (IA: Inhab A). {
      destruct l; rew_list in Hcond; try math.
      apply Inhab_of_val; auto.
    }
    xif;=> Hltn.
    + xval.
      xapp. { apply int_index_prove; try math. }
      xapp; try math; intros arr data Hdata.
      xapp;=> pos.
      xlet as;=> tmp Htmp.
      xapp (array_iter_spec tmp a l
              (fun (t: list A) =>
                  arr ~> Array (take i t ++ drop (length (take i t)) data) \*
                  pos ~~> length t
           )). {
        intros v t r Hvtr. apply Htmp; clear Htmp.
        xapp.
        xif;=> Htmp_cond.
        - xapp. {
            apply int_index_prove; try math.
            rewrite <- length_eq; rew_list.
            rewrite take_ge; try math.
            rewrite length_drop_nonneg; rewrite Hdata, length_make; try math.
          }
          xsimpl*; rew_list; try math.
          rewrite take_ge; try math.
          rewrite (@update_app_r _ _ 0 _ (length t)); auto; try math.
          rewrite take_ge; rew_list; try math.
          f_equal.
          apply (eq_of_extens IA).
          + rew_list; rewrite length_update, Hdata, ?length_drop_nonneg; rewrite ?length_make; try math.
          + intros j. rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Hdata, length_make; try math.
            intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_update_same; auto; try apply int_index_prove; try math.
          rewrite <- length_eq, length_drop_nonneg; rewrite length_make; try math.
          rewrite read_update_neq, !read_drop; auto; try (f_equal; math).
          rewrite length_make; math.
          rewrite length_make; math.
          apply int_index_prove; try math.
          rewrite <- length_eq,  length_drop_nonneg, length_make; try math.
          rewrite length_make; math.
        - xvals*; rew_list; try math.
          rewrite length_take_nonneg; try math.
          rewrite length_take_nonneg; rew_list; try math.
          rewrite take_app_l; auto; try math.
      }
      rewrite take_nil, length_nil, drop_zero, app_nil_l; auto.
      xvals*.
      rewrite length_take_nonneg; try math.
      rewrite <- app_nil_r, Hdata; f_equal.
      rewrite <- (@length_make _ i l[0]) at 1; try math.
      rewrite drop_at_length; auto.
    + xval.
      xapp. { apply int_index_prove; try math. }
      xapp; try math; intros arr data Hdata.
      xapp;=> pos.
      xlet as;=> tmp Htmp.
      xapp (array_iter_spec tmp a l
              (fun (t: list A) =>
                  arr ~> Array (take i t ++ drop (length (take i t)) data) \*
                  pos ~~> length t
           )). {
        intros v t r Hvtr. apply Htmp; clear Htmp.
        xapp.
        xif;=> Htmp_cond.
        - xapp. {
            apply int_index_prove; try math.
            rewrite <- length_eq; rew_list.
            rewrite take_ge; try math.
            rewrite length_drop_nonneg; rewrite Hdata, length_make; try math.
          }
          xsimpl*; rew_list; try math.
          rewrite take_ge; try math.
          rewrite (@update_app_r _ _ 0 _ (length t)); auto; try math.
          rewrite take_ge; rew_list; try math.
          f_equal.
          apply (eq_of_extens IA).
          + rew_list; rewrite length_update, Hdata, ?length_drop_nonneg; rewrite ?length_make; try math.
          + intros j. rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Hdata, length_make; try math.
            intros Hlen. rewrite read_cons_case.
          case (Z.eqb_spec j 0); intros Hj;
            [rewrite If_l, Hj| rewrite If_r]; auto.
          rewrite read_update_same; auto; try apply int_index_prove; try math.
          rewrite <- length_eq, length_drop_nonneg; rewrite length_make; try math.
          rewrite read_update_neq, !read_drop; auto; try (f_equal; math).
          rewrite length_make; math.
          rewrite length_make; math.
          apply int_index_prove; try math.
          rewrite <- length_eq,  length_drop_nonneg, length_make; try math.
          rewrite length_make; math.
        - xvals*; rew_list; try math.
          assert (i >= length l) by math.
          assert (length l > length t) by (rewrite Hvtr; rew_list; try math).
          assert (i >= length t) by math.
          rewrite take_ge; try math.
      }
      rewrite take_nil, length_nil, drop_zero, app_nil_l; auto.
      xvals*.
      rewrite take_ge; try math.
      rewrite Hdata.
      rewrite <- (@length_make _ (length l) l[0]) at 1; try math.
      rewrite drop_at_length, app_nil_r; auto.
Qed.

Fixpoint filter_not (A: Type) (fp: A -> Prop) (ls: list A) : list A :=
  match ls with
  | nil => nil
  | h :: t =>
      If fp h
      then filter_not fp t
      else h :: filter_not fp t
  end.

Lemma filter_not_nil_eq_list_filter (A: Type) (fp: A -> bool) (ls: list A):
   filter_not fp ls = List.filter (fun (vl: A) => ! (fp vl)) ls.
Proof.
  induction ls; auto.
  simpl.
  case_eq (fp a); intros Hfp; simpl; [rewrite If_l| rewrite If_r];
    rewrite ?IHls; auto.
Qed.  
  
Lemma filter_not_cons:
  forall (A : Type) (x : A) (l : list A) (P : A -> Prop),
       filter_not P (x :: l) =
         (If P x then filter_not P l else x :: filter_not P l).
Proof.
  intros; simpl; auto.
Qed.

Lemma filter_not_nil_eq_filter (A: Type) (fp: A -> Prop) (ls: list A):
   filter_not fp ls = filter (fun (vl: A) => ~ (fp vl)) ls.
Proof.
  induction ls; auto;
  rewrite filter_cons, filter_not_cons.
  case_eq (classicT (fp a));=> Hfp _.
  - rewrite If_r; auto.
  - rewrite If_l; auto.
    rewrite IHls; auto.
Qed.  
  
Lemma filter_not_nil:
  forall [A : Type] (P : A -> Prop), filter_not P nil = nil.
Proof.
  simpl; auto.
Qed.

Lemma filter_not_rev:
  forall [A : Type] (l : list A) (P : A -> Prop),
  filter_not P (rev l) = rev (filter_not P l).
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  rewrite filter_rev; auto.
Qed.  

Lemma LibList_length_filter_not:
  forall [A : Type] (l : list A) (P : A -> Prop),
  LibList.length (filter_not P l) <= LibList.length l.
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply LibList.length_filter.
Qed.

Lemma length_filter_not:
  forall [A : Type] (l : list A) (P : A -> Prop),
  length (filter_not P l) <= length l.
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply length_filter.
Qed.

Lemma mem_filter_not_eq:
  forall [A : Type] (x : A) (P : A -> Prop) (l : list A),
  mem x (filter_not P l) = (mem x l /\ ~ P x).
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply mem_filter_eq.
Qed.

Lemma filter_not_app:
  forall [A : Type] (l1 l2 : list A) (P : A -> Prop),
  filter_not P (l1 ++ l2) = filter_not P l1 ++ filter_not P l2.
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  apply filter_app.
Qed.

Lemma filter_not_length_partition:
  forall [A : Type] (P : A -> Prop) (l : list A),
  length (filter_not (fun x : A => P x) l) +
  length (filter_not (fun x : A => ~ P x) l) <= length l.
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  apply filter_length_partition.
Qed.
  
Lemma filter_not_last:
  forall [A : Type] (x : A) (l : list A) (P : A -> Prop),
  filter_not P (l & x) = filter_not P l ++
                           (If P x then nil else x :: nil).
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  rewrite filter_last.
  repeat f_equal.
  case_eq (classicT (P x));=> Hfp _.
  - rewrite If_r; auto.
  - rewrite If_l; auto.
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
