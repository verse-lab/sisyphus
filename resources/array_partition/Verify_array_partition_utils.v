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
