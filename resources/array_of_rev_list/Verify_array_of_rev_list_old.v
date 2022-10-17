Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Utils Tactics. 

From Common Require Import Verify_combinators. 
From Common Require Import Verify_list. 

From ProofsArrayOfRevList Require Import Array_of_rev_list_old_ml.
    
Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
  xcf.
  case l as [ | x l'] eqn: H.
  - xmatch_case_0.
    xvalemptyarr.
  - xmatch.
    xletopaque len Hlen.
    xalloc arr data Hdata.
    xref r.
    xletopaque tmp Htmp.
    xapp (for_downto_spec (len - 2) 0 tmp
            (fun (i: int) =>
               r ~> Ref (drop (len - (i + 1)) l) \*
                 arr ~> Array (take (i + 1) data ++ rev (take (len - (i + 1)) l)))).
    { rewrite Hlen; rew_list; math. }
    {
      intros i Hi_vld; apply Htmp; clear Htmp.
      rewrite Hlen in Hi_vld; rew_list in Hi_vld.
      xapp.
      xapp (hd_spec); try rewrite length_drop_nonneg; try (rewrite Hlen, H; rew_list; math).
      xapp. {
        apply int_index_prove; try math.
        rewrite <- length_eq; rew_list.
        rewrite length_take_nonneg; try (rewrite Hdata, length_make, Hlen; rew_list; try math).
        rewrite length_take_nonneg; try (rewrite Hlen; rew_list; try math).
        rewrite H; rew_list; math.
      }
      xunit.
      xapp (tl_spec); try rewrite length_drop_nonneg; try (rewrite Hlen, H; rew_list; math).
      xapp.
      pose (IA:= Inhab_of_val x).
      assert (Hlen': len = length l) by (rewrite H, Hlen; rew_list; auto).
      xmatch; xvals*.
      - rewrite drop_drop; try (rewrite Hlen; rew_list); try math; f_equal; math.
      - rewrite update_app_l; [| (rewrite length_take_nonneg; try (rewrite Hdata, length_make, Hlen; rew_list; try math); math) ].
        rewrite (take_pos_last IA); [| apply int_index_prove; rewrite <-?length_eq, ?Hdata, ?length_make, ?Hlen; rew_list; try math].
        math_rewrite (i + 1 - 1 = i); math_rewrite (i - 1 + 1 = i).
        rewrite (@update_app_r _ _ 0 _ i i); try math; [| rewrite length_take_nonneg; rewrite ?Hdata, ?length_make, ?Hlen; rew_list; try math ].
        rewrite update_zero, app_last_l.
        rewrite read_drop; [| rewrite Hlen, H; rew_list; math | apply int_index_prove; rewrite ?Hlen'; rew_list; try math ].
        f_equal.
        apply (eq_of_extens IA).
        + rew_list. rewrite !length_take_nonneg; rewrite ?Hlen, ?H; rew_list; math.
        + intros j. rewrite index_eq_index_length, int_index_eq; rew_list.
          rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; math].
          math_rewrite (1 + (len - (i + 1)) = len - i); rewrite Hlen'.
          intros Hj.
          case (Z.eqb_spec j 0);=> Heq.
          * rewrite Heq; rewrite read_zero.
            rewrite read_rev; [ | try (rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; math]); math ].
            rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; try math].
            rewrite read_take; try math; try apply int_index_prove; try math.
            f_equal; math.
          * rewrite read_cons_pos; try math.
            rewrite read_rev; [ | try (rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; math]); math ].
            rewrite read_rev; [ | try (rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; math]); math ].
            rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; try math].
            rewrite length_take_nonneg; [| rewrite ?Hlen, ?H; rew_list; try math].
            rewrite read_take; try math; try apply int_index_prove; try math.
            rewrite read_take; try math; try apply int_index_prove; try math.
            f_equal.
            math.
    }
    {
      pose (IA:= Inhab_of_val x).
      math_rewrite  ((len - 2 + 1) = len - 1).
      math_rewrite ((len - (len - 1)) = 0 + 1).
      rewrite H, drop_cons, drop_zero; try math; auto.
    } {
      rewrite Hdata, take_make_eq; try (rewrite Hlen; rew_list; math).
      math_rewrite  (len - (len - 2 + 1) = 0 + 1).
      rewrite H, take_cons, take_zero; try math; rew_list.
      math_rewrite (len = (len - 1) + 1).
      math_rewrite  ((len - 1 + 1) - 2 + 1 = len - 1).
      apply make_succ_r.
      rewrite Hlen; rew_list; math.
    }
    xunit.
    xsimpl.
    {
      math_rewrite ((0 - 1 + 1) = 0); math_rewrite (len - 0 = len).
      rewrite take_zero. rewrite Hlen, H, take_full_length; rew_list; auto.
    }
Qed.
