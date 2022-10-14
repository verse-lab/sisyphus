Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Require Import Utils.

Ltac sis_solve_start :=
  repeat lazymatch goal with
  | [ |- forall (Heq: _ = _), _] => intros Heq
  | [ |- forall (x: _), _] => intros x
  | [ H : Wpgen_body _ |- @Triple ?f ?r ?r2 ?P ?Q ] => apply H; clear H; xgo*
  end.  

Ltac sis_handle_if :=
  lazymatch goal with
    | [ H : ?cond |- context [If ?cond then _ else _]] => rewrite If_l; auto
    | [ H : ?cond |- context [If (~ ?cond) then _ else _]] => rewrite If_r; auto
    | [ H : ~ ?cond |- context [If ?cond then _ else _]] => rewrite If_r; auto
    | _ => idtac
    end.  

Create HintDb filter_lemmas.
Create HintDb iff_lemmas.

#[export] Hint Resolve mem_filter : filter_lemmas.
#[export] Hint Resolve length_filter : filter_lemmas.
#[export] Hint Resolve mem_filter_inv : filter_lemmas.
#[export] Hint Resolve LibList.length_filter : filter_lemmas.
#[export] Hint Resolve Exists_filter_pred_incl : filter_lemmas.
#[export] Hint Resolve filter_length_partition : filter_lemmas.
#[export] Hint Resolve LibList.length_filter_eq_mem_ge_one : filter_lemmas.
#[export] Hint Resolve length_filter_eq_mem_ge_one : filter_lemmas.

#[export] Hint Rewrite filter_not_nil : filter_lemmas.
#[export] Hint Rewrite filter_not_rev : filter_lemmas.
#[export] Hint Rewrite LibList_length_filter_not : filter_lemmas.
#[export] Hint Rewrite length_filter_not : filter_lemmas.
#[export] Hint Rewrite filter_not_nil_eq_filter : filter_lemmas.
#[export] Hint Rewrite filter_not_app : filter_lemmas.
#[export] Hint Rewrite mem_filter_not_eq : filter_lemmas.
#[export] Hint Rewrite filter_not_length_partition : filter_lemmas.
#[export] Hint Rewrite filter_not_cons : filter_lemmas.
#[export] Hint Rewrite filter_not_last : filter_lemmas.
#[export] Hint Rewrite filter_nil : filter_lemmas.
#[export] Hint Rewrite filter_rev : filter_lemmas.
#[export] Hint Rewrite count_eq_length_filter : filter_lemmas.
#[export] Hint Rewrite LibList.count_eq_length_filter : filter_lemmas.
#[export] Hint Rewrite filter_not_nil_eq_filter : filter_lemmas.
#[export] Hint Rewrite mem_filter_eq : filter_lemmas.
#[export] Hint Rewrite filter_app : filter_lemmas.
#[export] Hint Rewrite LibList.filter_length_partition : filter_lemmas.
#[export] Hint Rewrite filter_cons : filter_lemmas.
#[export] Hint Rewrite LibList.filter_length_two_disjoint : filter_lemmas.
#[export] Hint Rewrite filter_length_two_disjoint : filter_lemmas.
#[export] Hint Rewrite filter_last : filter_lemmas.

#[export] Hint Rewrite If_istrue : iff_lemmas.
#[export] Hint Rewrite If_r : iff_lemmas.
#[export] Hint Rewrite If_l : iff_lemmas.

