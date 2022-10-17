Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.
From Common Require Import Verify_combinators Verify_opt.

From ProofsArrayIsSorted Require Import Array_is_sorted_old_ml.

Lemma array_is_sorted_spec :
  forall (a : array int) (l : list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as cond.
  - xvals*. { sis_list_solver. }
  - xletopaque tmp Htmp.
    xapp (until_downto_spec (length l - 1) 0 tmp
            (fun (i: int) (b: option unit) =>
               \[b = opt_of_bool (negb (is_sorted (drop i l)))] \*
                 a ~> Array l)
         ). {
    intros i Hi.
    apply Htmp; clear Htmp.
    xpull;=>Hopt.
    xapp. { sis_handle_int_index_prove. }
    xapp. { sis_handle_int_index_prove. }
    xif;=> Hif.
    - xvals*. {
        rewrite (@drop_cons_unfold _ Inhab_int); try math.
        apply opt_of_bool_none_intro; apply opt_of_bool_none in Hopt.
        apply Bool.negb_true_iff; rewrite Bool.negb_involutive.
        apply Bool.negb_true_iff in Hopt; rewrite Bool.negb_involutive in Hopt.
        rewrite bool_eq_true_eq in *.
        apply is_sorted_gen;
          math_rewrite (i - 1 + 1 = i);
          auto;
          try (rewrite <- Hexists; auto);
          rewrite ?length_drop_nonneg; try math;
          rewrite ?drop_drop, ?read_drop, Z.add_0_r;
          auto; math.
      }
    - xvals*. {
        apply opt_of_bool_some_intro; apply Bool.negb_true_iff; apply negb_iff. 
          eapply (@not_is_sorted_gen _ 1);
            rewrite ?length_drop_nonneg; rewrite ?read_drop;
            try apply int_index_prove; try math.
          math_rewrite (i - 1 + (1 - 1) = i - 1).
          math_rewrite (i - 1 + 1 = i).
          math.
      }
    } { math. } {
      apply opt_of_bool_none_intro; apply Bool.negb_true_iff; rewrite Bool.negb_involutive.
      rewrite is_sorted_last_elt; auto.
      math.
    }
    intros term i Hcond Heq.
    xapp (opt_is_some_spec).
    xvals*. {
      subst.
      rewrite is_some_opt_of_bool_eq, <- negb_eq_neg, Bool.negb_involutive in *.
      case_eq ((is_sorted (drop i l)));=> Heq.
      - rewrite Heq in *; simpl in *; destruct Hcond as [Hlen Heq0].
        assert (Heq0last: i = 0) by (apply Z.eqb_eq; auto).
        rewrite Heq0last in Heq; rewrite drop_zero in Heq; auto.
      - rewrite <- (@list_eq_take_app_drop _ i l); try math.
        rewrite is_sorted_app_r; auto.
    }
Qed.
