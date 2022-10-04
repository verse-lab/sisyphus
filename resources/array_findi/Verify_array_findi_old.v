Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
From ProofsArrayFindi Require Import Verify_array_findi_utils.
From ProofsArrayFindi Require Import array_findi_old_ml.

Lemma array_findi_spec :
  forall (A : Type) `{EA : Enc A}
         (a : array A) (f : func) (l : list A) (fp: int -> A -> bool),
    (forall (i: int)(a: A), 0 <= i < length l ->
        SPEC_PURE (f i a)
         POST (fun (b: bool) => \[b = fp i a])) ->
  SPEC (findi a f)
  PRE (a ~> Array l)
  POST (fun (b : option (int * A)) =>
          \[b = ProofsArrayFindi.Verify_array_findi_utils.findi 0 fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (@until_upto_spec _ _  0 (length l) tmp
          (fun i b => \[b = ProofsArrayFindi.Verify_array_findi_utils.findi 0 fp (take i l)] \*
                         a ~> Array l)
       ). {
    intros i Hi.
    apply Htmp.
    assert (IA: Inhab A). {
      destruct l; rew_list in Hi; try math.
      apply Inhab_of_val; auto.
    }
    xpullpure Hexists.
    xapp. { apply int_index_prove; math. }
    xapp (H i l[i]). { math. }
    xif;=> Hif.
    xapp. { apply int_index_prove; math. }
    xvals. {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite findi_app_r; auto; simpl.
      rewrite length_take_nonneg; try math.
      math_rewrite (0 + i = i).
      rewrite Hif; simpl; auto.
    }
    xvals*.
    {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite findi_app_r; auto; simpl.
      rewrite length_take_nonneg; try math.
      math_rewrite (0 + i = i).
      case_eq (fp i l[i]) ;=> Hfp; simpl; auto.
      rewrite Hfp in Hif.
      contradiction Hif; auto.
    }
  }
  { math.  }
  { rewrite take_zero; simpl; auto. }
  intros [[i_nd i_vl]|] i_b [Hlen Himpl] Hexists; xsimpl*; simpl in Himpl.
  - simpl in Hexists.
    rewrite <- (@list_eq_take_app_drop _ i_b l) at 1; try math.
    rewrite findi_app_l; auto; simpl.
    rewrite <- Hexists; simpl; auto.
  - assert (Heq: i_b = length l) by (apply Z.eqb_eq; auto).
    rewrite Heq,take_full_length in Hexists; auto. 
Qed.
