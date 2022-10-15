Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators Verify_opt.

From Common Require Import Tactics Utils Solver.

From ProofsArrayIsSorted Require Import Array_is_sorted_old_ml.

Fixpoint is_sorted_internal_rec last_value ls :=
  match ls with
  | h :: t =>
      if h <=? last_value
      then is_sorted_internal_rec h t
      else false
  | nil => true
  end.

Definition is_sorted ls :=
  match ls with
  | h :: t => is_sorted_internal_rec h t
  | nil => true
  end.

Lemma is_sorted_internal_pres v ls :
    is_sorted_internal_rec v ls = true ->
    is_sorted ls = true.
Proof.
  case ls as [| x xs]; simpl; auto.
  case (x <=? v); intro H; try inversion H; auto.
Qed.


Lemma array_is_sorted_spec :
  forall (a: array int) (l: list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[ b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as Hcond.
  - xvals*. { sis_list_solver. }
  - xletopaque tmp Htmp.
    xapp (until_downto_spec (length l - 1) 0 tmp
            (fun (i: int) (res: option unit) =>
               a ~> Array l \*
                 \[res = opt_of_bool (negb (is_sorted (take (length l - i) (rev l))))]
            )
         ). {
      sis_solve_start; sis_normalize_opt_of_bool; sis_normalize_boolean_goals.
      gen H.
      admit.
      admit.
    } { math. } {
      sis_normalize_opt_of_bool; sis_normalize_boolean_goals.
      math_rewrite (length l - (length l - 1) = 0 + 1).
      case (rev l); [ | intros h t ]; rewrite ?take_nil, ?take_cons_pos; auto; try math.
    }
  intros res i Hterm Heq.
  xapp (opt_is_some_spec).
  xlet.
  xvals*. {
    gen Hterm; subst; sis_normalize_opt_of_bool;
      rewrite Bool.negb_involutive; intros Hterm.
    rewrite <- negb_eq_neg, Bool.negb_involutive.
    case_eq (is_sorted (take (length l - i) (rev l))).

    admit.
  }
Admitted.
