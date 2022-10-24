Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.
From Common Require Import Verify_opt.

From ProofsArrayFindi Require Import Array_findi_new_ml.

Lemma array_findi_spec :
  forall (A : Type) `{EA : Enc A}
         (a : array A) (f : func) (l : list A) (fp: int -> A -> bool),
    (forall (i: int)(a: A), 0 <= i < length l ->
        SPEC_PURE (f i a)
         POST (fun (b: bool) => \[b = fp i a])) ->
  SPEC (findi a f)
  PRE (a ~> Array l)
  POST (fun (b : option (int * A)) =>
          \[b = list_findi fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as Hcond.
  - xvals. {
      apply length_zero_inv in Hcond; rewrite Hcond, findi_unfold; simpl; auto.
    }
  - xinhab.
    xref found.
    xref idx.
    xapp. { apply int_index_prove; try rewrite <- length_eq; rew_list; math. }
    xref value.
    xletopaque tmp Htmp.
    xapp (while_upto_spec 0 (length l) tmp
            (fun (i: int) (b: bool) =>
               \[b = negb (is_some (list_findi fp (take i l)))] \*
               a ~> Array l \*
               value ~~> option_value_snd l[0] (list_findi fp (take i l)) \*
               idx ~~> option_value_fst 0 (list_findi fp (take i l)) \*
               found ~~> negb b
         )). {
      intros i Hi; apply Htmp; clear Htmp.
      xpull;=> Hneg.
      xapp. { apply int_index_prove; try rewrite <- length_eq; math. }
      xapp (H i l[i]). { auto. }
      xif;=> vl.
      xapp.
      xapp. { apply int_index_prove; try rewrite <- length_eq; math. }
      xapp.
      xapp.
      xvals*. {
        rewrite findi_unfold.
        rewrite (take_pos_last IA);
          try apply int_index_prove;
          try rewrite <- length_eq; try math.
        rewrite findi_app_r; auto; simpl.
        math_rewrite ((i + 1 - 1) = i).
        rewrite length_take_nonneg; try math.
        math_rewrite (0 + i = i).
        rewrite vl; simpl; auto.
        math_rewrite ((i + 1 - 1) = i).
        apply (f_equal negb) in Hneg.
        rewrite Bool.negb_involutive, findi_unfold in Hneg; simpl in Hneg.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
      }
      {
        rewrite findi_unfold.
        rewrite (take_pos_last IA);
          try apply int_index_prove;
          try rewrite <- length_eq; try math.
        rewrite findi_app_r; auto; simpl.
        math_rewrite ((i + 1 - 1) = i).
        rewrite length_take_nonneg; try math.
        math_rewrite (0 + i = i).
        rewrite vl; simpl; auto.
        math_rewrite ((i + 1 - 1) = i).
        apply (f_equal negb) in Hneg.
        rewrite Bool.negb_involutive, findi_unfold in Hneg; simpl in Hneg.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
      }
      {
        rewrite findi_unfold.
        rewrite (take_pos_last IA);
          try apply int_index_prove;
          try rewrite <- length_eq; try math.
        rewrite findi_app_r; auto; simpl.
        math_rewrite ((i + 1 - 1) = i).
        rewrite length_take_nonneg; try math.
        math_rewrite (0 + i = i).
        rewrite vl; simpl; auto.
        math_rewrite ((i + 1 - 1) = i).
        apply (f_equal negb) in Hneg.
        rewrite Bool.negb_involutive, findi_unfold in Hneg; simpl in Hneg.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
      }
      - xvals*. {
          assert (Hfalse: fp i l[i] = false) by (gen vl; case (fp i l[i]); auto; intro Hfalse; contradiction Hfalse; auto).
          rewrite findi_unfold in *; simpl in *.
          rewrite (take_pos_last IA);
            try apply int_index_prove;
            try rewrite <- length_eq; try math.
          rewrite findi_app_r; auto; simpl.
          math_rewrite ((i + 1 - 1) = i).
          rewrite length_take_nonneg; try math.
          math_rewrite (0 + i = i).
          rewrite Hfalse; simpl; auto.
        math_rewrite ((i + 1 - 1) = i).
        apply (f_equal negb) in Hneg.
        rewrite Bool.negb_involutive in Hneg; simpl in Hneg.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
        }
        {
          f_equal; symmetry.
          assert (Hfalse: fp i l[i] = false) by (gen vl; case (fp i l[i]); auto; intro Hfalse; contradiction Hfalse; auto).
          rewrite !findi_unfold in *; simpl in *.
          rewrite (take_pos_last IA);
            try apply int_index_prove;
            try rewrite <- length_eq; try math.
          rewrite findi_app_r; auto; simpl.
          math_rewrite ((i + 1 - 1) = i).
          rewrite length_take_nonneg; try math.
          math_rewrite (0 + i = i).
          rewrite Hfalse; simpl; auto.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
        math_rewrite ((i + 1 - 1) = i).
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
        }
        {
          f_equal; symmetry.
          assert (Hfalse: fp i l[i] = false) by (gen vl; case (fp i l[i]); auto; intro Hfalse; contradiction Hfalse; auto).
          rewrite !findi_unfold in *; simpl in *.
          rewrite (take_pos_last IA);
            try apply int_index_prove;
            try rewrite <- length_eq; try math.
          rewrite findi_app_r; auto; simpl.
          math_rewrite ((i + 1 - 1) = i).
          rewrite length_take_nonneg; try math.
          math_rewrite (0 + i = i).
          rewrite Hfalse; simpl; auto.
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
        math_rewrite ((i + 1 - 1) = i).
        gen Hneg.
        case (list_findi_internal 0 fp (take i l)); simpl; intros; auto.
        inversion Hneg.
        }
    }
    { math. }
    { rewrite take_zero; simpl; auto. }
    intros res i_b Hres Hexists.
    xmatch.
    xapp.
    xif as Hlcond.
    + xapp.
      xapp.
      xvals*. {
        destruct Hres as [Hlen Himpl].
        simpl in *.
        apply (f_equal negb) in Hexists.
        rewrite Bool.negb_involutive in Hexists; simpl in Hexists.
        symmetry.
        rewrite <- (@list_eq_take_app_drop _ i_b l) at 1; try math.
        rewrite !findi_unfold, findi_app_l in *; auto; simpl.
        gen Hexists.
        case (list_findi_internal 0 fp (take i_b l)) as [[p1 p2] |]; simpl; intros; auto.
        inversion Hexists.
        rewrite <- Hexists; auto.
      }
    + xvals*. {
        simpl in *.
        destruct Hres as [Hlen Himpl].
        assert (Heqv: i_b = length l) by (apply Z.eqb_eq; auto).
        rewrite Heqv in *.
        rewrite take_full_length in *.
        apply (f_equal negb) in Hexists.
        rewrite Bool.negb_involutive in Hexists; simpl in Hexists.
        gen Hexists.
        case ((list_findi fp l)); simpl; intros; auto.
        inversion Hexists.
      }
Qed.
