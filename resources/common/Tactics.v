Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.


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

Ltac xinhab_inner A :=
  match goal with
  | [ l : list A |- _ ] =>
      let IA := fresh "IA" in
      (assert (IA: Inhab A); [
          (try apply Inhab_of_val;
           destruct l;
           rew_list in *;
           try math; auto; fail)
        | ]) || (idtac "xinhab failed"; fail)
  end.

  Ltac xinhab :=
    lazymatch goal with
    | [ l : list ?A |- _ ] =>
        let IA := fresh "IA" in
        (assert (IA: Inhab A); [
            (try apply Inhab_of_val;
             destruct l;
             rew_list in *;
             try math; auto; fail)
          | ]) || (idtac "xinhab failed"; fail)
    | _ => idtac "not found"
    end || idtac.


  Ltac xif_pat Hcond :=
    let cond := fresh "Hcond" in
    lazymatch goal with
    | [|- context [Wpgen_if (negb ?v) _]] =>
        xif;=> cond;
        [ assert (Hcond: v = false);
          [ destruct v; auto; contradiction cond; simpl; auto | rewrite Hcond in * ] |
          assert (Hcond: v = true);
          [ destruct v; auto; contradiction cond; simpl; auto | rewrite Hcond in *] 
        ]
    | _ => fail
    end.

  Ltac xif_intros :=
    let cond := fresh "Hcond" in
    xif; lazymatch goal with
    | [|- _ -> himpl _ _] => intros cond
    | _ => fail
    end.


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

  Tactic Notation "xref"
    simple_intropattern(r) :=
    xapp; intros r.

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


  Tactic Notation "xunit" :=
    xmatch; [xapp || xval].

  Tactic Notation "xletopaque"
    simple_intropattern(idx)
    simple_intropattern(Hidx) :=
    xlet as;=> idx Hidx.

  Tactic Notation "xvalemptyarr" :=
    xapp; xsimpl.

  Tactic Notation "xif" "as" simple_intropattern(Hcond)  :=
    let cond_var := fresh Hcond in
    let var := fresh Hcond in
    let Hvar := fresh Hcond in
    (xlet as;=> var Hvar;
     xif;=> cond_var;
     rewrite Hvar,istrue_isTrue_eq in cond_var;
     clear Hvar var) || xif_pat Hcond || xif_intros.
