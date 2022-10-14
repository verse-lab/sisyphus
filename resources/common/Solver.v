Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Require Import Utils Tactics.

Create HintDb filter_lemmas.
Create HintDb iff_lemmas.

#[export] Hint Resolve length_zero_inv: filter_lemmas.
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

Ltac sis_solve_start :=
  repeat lazymatch goal with
  | [ |- forall (Heq: _ = _), _] => let x := fresh Heq in intro x
  | [ |- forall (x: _), _] => let x := fresh x in intro x
  | [ |- _ -> _ ] => let v := fresh "Hv" in intros v
  | [ H : Wpgen_body _ |- @Triple ?f ?r ?r2 ?P ?Q ] => apply H; clear H; xinhab; xgo*
  end.

Ltac sis_handle_if :=
  lazymatch goal with
    | [ H : ?cond |- context [If ?cond then _ else _]] => rewrite If_l; auto
    | [ H : ?cond |- context [If (~ ?cond) then _ else _]] => rewrite If_r; auto
    | [ H : ~ ?cond |- context [If ?cond then _ else _]] => rewrite If_r; auto
    | _ => idtac
    end.  

Ltac sis_list_solver :=
  lazymatch goal with
  | [ H : length _ = 0  |- _ ] =>
      apply length_zero_inv in H; try rewrite H in *; rew_list in *; auto
  | [ |- context[ take 0 _ ] ] =>
      rewrite take_zero in *; rew_list; simpl
  | [ |- context[ take (length ?l) ?l ] ] =>
      rewrite take_full_length; rew_list; simpl
  end.  

Ltac sis_expand_rewrites :=
  repeat lazymatch goal with
    | [ H: ?x = _ |- context [?x]] => rewrite !H in *
    end.

Ltac sis_handle_int_index_prove :=
  lazymatch goal with
  | [ |- index _ _ ] => apply int_index_prove; try rewrite <- !length_eq; try math
  | _ => idtac
  end.

Ltac sis_normalize_length :=
  lazymatch goal with
  | [ |- context [length (take _ _)] ] =>
      rewrite length_take_nonneg; sis_normalize_length; rew_list; try math
  | [ |- context [length (drop _ _)] ] =>
      rewrite length_drop_nonneg; sis_normalize_length; rew_list; try math
  | [ |- context [length (make _ _)] ] =>
      rewrite length_make; sis_normalize_length; rew_list; try math
  | _ => idtac
  end.

Ltac sis_dispatch_filter_goal :=
  match goal with
  | [ |- context [ length (filter ?f ?ls) ]] =>
      pose proof (length_filter ls f); math
  end.

Ltac sis_handle_list_update :=
  lazymatch goal with
  | [ |- context [ (?l ++ _)[length ?l := _] ]] =>
      rewrite (@update_app_r _ _ 0 _ (length l)); try math
  end.

Ltac sis_normalize_succs :=
  repeat lazymatch goal with
    | [ |- context [ (1 + ?x) ]] =>
        math_rewrite (1 + x = x + 1)
    | [ |- context [ ?x + (?y + 1) ]] =>
        math_rewrite (x + (y + 1) = (x + y) + 1)
    end.
