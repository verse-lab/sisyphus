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

Ltac intros_then_apply H :=
  lazymatch goal with
  | [ |- forall (x: _), _] => let x := fresh x in intro x; intros_then_apply H; gen x
  | _ => H
  end.

Ltac sis_simplify_math_goal :=
  rew_list;
  repeat lazymatch goal with
    | [ |- context[?x - 0] ] => math_rewrite (x - 0 = x)
    | [ |- context[?x - ?x] ] => math_rewrite (x - x = 0)
    | [ |- context[0 + ?x]] => math_rewrite (0 + x = x)
    | [ |- context[?x + 1 - 1]] => math_rewrite (x + 1 - 1 = x)
    | [ |- context[?x + 1 - 2 + 1]] => math_rewrite (x + 1 - 2 + 1 = x)
    | [ |- context [ (1 + ?x) ]] =>
        math_rewrite (1 + x = x + 1)
    | [ |- context [ ?x + (?y + 1) ]] =>
        math_rewrite (x + (y + 1) = (x + y) + 1)
    | [ |- context[(?z + ?x + ?y) - (?x + ?y)] ] =>
        math_rewrite (z + x + y - (x + y) = z)
    | [ |- context[ (?t + ?r - ?t)]] =>
        math_rewrite ((t + r - t) = r)
    | [ |- context[ (?t + ?r + ?z - ?t)]] =>
        math_rewrite ((t + r + z - t) = r + z)
    | [ |- context [(?x + 1 + 1 - 2)]] =>
        math_rewrite (x + 1 + 1 - 2 = x)
    | [ |- context[?r + 1 - (?t + 1)]] =>
        math_rewrite (r + 1 - (t + 1) = r - t)
    | [ |- context[?r - 1 + ?z + 1]] =>
        math_rewrite (r - 1 + z + 1 = r + z)
    | [ |- context[?b + ?x + ?y - ?x]] =>
        math_rewrite (b + x + y - x = b + y)
    | [ |- context[?x + 1 - 2 - ?z + 1] ] => math_rewrite (x + 1 - 2 - z + 1 = x - z)
    end.

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


Ltac sis_expand_rewrites :=
  repeat lazymatch goal with
    | [ H: ?x = _ |- context [?x]] => rewrite !H in *
    end.

Ltac sis_handle_int_index_prove :=
  lazymatch goal with
  | [ |- index _ _ ] => apply int_index_prove; try rewrite <- !length_eq; rew_list; try math
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
  | [ H : _ = rev ?rest |- context[length ?rest] ] =>
      apply (f_equal (@rev _)) in H; rewrite rev_rev in H; rewrite <- H; rew_list;
      sis_normalize_length; rew_list; try math
  | _ => idtac
  end.

Ltac sis_list_solver :=
  repeat lazymatch goal with
  | [ H : 0 = length _ |- _ ] =>
      symmetry in H; apply length_zero_inv in H; try rewrite H in *; rew_list in *; auto
  | [ H : length _ = 0  |- _ ] =>
      apply length_zero_inv in H; try rewrite H in *; rew_list in *; auto
  | [ |- context[ take 0 _ ] ] =>
      rewrite take_zero in *; rew_list; simpl
  | [ |- context[ take (length ?l) ?l ] ] =>
      rewrite take_full_length; rew_list; simpl
  | [ |- context[drop _ (make _ _)]] =>
      rewrite drop_make_eq; [|subst;rew_list;math]
  | [ |- context[drop 1 (?hd :: _)]] =>
      rewrite (drop_cons_pos hd); [math_rewrite (1 - 1 = 0)| math];
      rewrite drop_zero
  | [ |- context[drop 1 (?hd :: _ ++ _)]] =>
      rewrite (drop_cons_pos hd); [math_rewrite (1 - 1 = 0)| math];
      rewrite drop_zero
  | [ |- context[drop 0 _]] =>
       rewrite drop_zero
  | [ |- context[make 0 _]] =>
       rewrite make_zero
  end.

Ltac sis_list_deep_solver :=
  repeat match goal with 
  | [ |- context[drop ?x (make ?z _ ++ _)]] =>
      let H := fresh "Hvalid" in
      assert (H: x >= z) by (subst; rew_list; sis_normalize_length; math); rewrite drop_app_r; [clear H|sis_normalize_length; math]
  | [ |- context[drop ?d (rev ?r ++ _)]] =>
      let H := fresh "Hlen" in
      assert (H: length (rev r) <= d) by (rew_list; math);
      rewrite drop_app_r; [clear H; rew_list| rew_list; math]
  | [ H: nil = rev ?x |- _ ] =>
      apply nil_eq_rev_inv in H; try (subst; rew_list; auto; fail)
  | [ |- context [(make (?i + 1) _ ++ _)[?i := _]]] =>
      rewrite make_succ_r; [ | math]; rew_list; rewrite update_middle; [|sis_normalize_length]
  | [ |- make (?i + 1) ?vl = make ?i ?vl & ?vl] =>
      rewrite make_succ_r; [ | math]; rew_list; auto
  | [ H: _ :: ?rest = ?ls |- context [length ?rest] ] =>
      let H_len := fresh "Hlen" in
      assert (H_len: length rest = length ls - 1) by (rewrite <- H; rew_list; math);
      rewrite H_len; clear H_len; rew_list
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

Ltac sis_normalize_opt_of_bool :=
      repeat lazymatch goal with
    | [ H:  None = opt_of_bool _ |- _ ] =>
        apply opt_of_bool_none in H
    | [ H:  Some tt = opt_of_bool _ |- _ ] =>
        apply opt_of_bool_some in H
    | [  |- Some tt = opt_of_bool _ ] =>
        apply opt_of_bool_some_intro
    | [ |- None = opt_of_bool _ ] =>
        apply opt_of_bool_none_intro
    | [ |- context [is_some (opt_of_bool _)]] =>
        rewrite is_some_opt_of_bool_eq
    end.

Ltac sis_normalize_boolean_goals :=
  repeat lazymatch goal with
    | [ H : negb _ = false |- _ ] =>
        apply (f_equal negb) in H; rewrite Bool.negb_involutive in H; simpl negb in H
    | [ H : negb _ = true |- _ ] =>
        apply (f_equal negb) in H; rewrite Bool.negb_involutive in H; simpl negb in H
    | [ |- negb _ = false ] =>
        rewrite (Bool.negb_involutive_reverse false); apply f_equal; simpl negb
    | [ |- negb _ = true ] =>
        rewrite (Bool.negb_involutive_reverse true); apply f_equal; simpl negb
    end.  

Ltac sis_handle_take_splitting_goals :=
  lazymatch goal with
    | [ H: context [take ?x _] |- context[take (?x - 1) _] ] =>
        gen H; erewrite take_pos_last; sis_handle_int_index_prove; auto; intros H
  | [ |- context [(take ?i _ ++ _)[?i := _]]] =>
      rewrite (@update_app_r _ _ 0 (take i _) i i); try math
  end.

Ltac sis_handle_take_drop_full_length :=
  lazymatch goal with
  | [ Heq: length ?x = length ?y |-
        context [ take (length ?x) (map2 ?fp (combine ?x ?y))]] =>
      let H := fresh "H" in
      assert (H: length x = length (map2 fp (combine x y))) 
        by (unfold map2; rewrite length_map, !length_eq, length_combine; gen Heq; rewrite !length_eq; math);
      rewrite H, ?take_full_length, ?drop_at_length
  | [  |- context [ drop (length ?x) (make (length ?x) ?vl)]] =>
      let H := fresh "H" in
      assert (H: length x = length (make (length x) vl))
        by (rewrite length_make; math);
      rewrite H at 1; rewrite drop_at_length
  end.


Ltac sis_generic_solver :=
  lazymatch goal with
  | [ |- context[@Triple _]] =>
      intros_then_apply sis_simplify_math_goal; sis_solve_start; sis_generic_solver
  | [ |- index _ _] => sis_handle_int_index_prove; sis_generic_solver
  | _ => subst;
         repeat (sis_normalize_length;
                 sis_list_solver;
                 sis_list_deep_solver;
                 sis_simplify_math_goal; auto)
  end.
