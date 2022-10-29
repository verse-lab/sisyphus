Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsArrayFindi Require Import Array_findi_old_ml.

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
  xletopaque tmp Htmp.
  xapp (until_upto_spec (int * A) 0 (length l) tmp
          (fun (i: int) (b: option (int * A)) =>
             \[b = list_findi fp (take i l)] \*
               a ~> Array l)
       ). {
    sis_solve_start. {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite findi_unfold, findi_app_r; auto; simpl.
      rewrite length_take_nonneg; try math.
      math_rewrite (0 + i = i).
      rewrite H1; simpl; auto.
    }
    {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite findi_unfold, findi_app_r; auto; simpl.
      rewrite length_take_nonneg; try math.
      math_rewrite (0 + i = i).
      case_eq (fp i l[i]) ;=> Hfp; simpl; auto.
      rewrite Hfp in H1.
      contradiction H1; auto.
    }
  }
  { sis_generic_solver.  }
  { sis_generic_solver. }
  intros res i_b Hres Hexists.
  xvals*. {
    destruct Hres as [Hlen Himpl].
    case res as [[i_nd i_vl]|]; simpl in Himpl;
    sis_generic_solver.
    - rewrite <- (@list_eq_take_app_drop _ i_b l) at 1; try math.
      rewrite findi_unfold, findi_app_l in *; auto; simpl.
      rewrite <- Hexists; simpl; auto.
  }
Qed.
