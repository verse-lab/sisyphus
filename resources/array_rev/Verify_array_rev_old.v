Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.


From ProofsArrayRev Require Import array_rev_old_ml.
From ProofsArrayRev Require Import Verify_array_rev_utils.


Lemma array_rev_spec :
  forall (A: Type) `{EA:Enc A} (a: loc)
         (l:list A),
 SPEC (rev a)
   PRE (a ~> Array l)
   POST (fun (_: unit) => a ~> Array (LibList.rev l)).
Proof using.
  intros A EA a l.
  xcf.
  xapp.
  xlet.
  xlet as; => loop Hloop_spec.
  pose proof (Hlen := Zdiv2_odd_eqn (length l));
      rewrite mult_2_eq_plus, <- Z.add_assoc, Z.div2_div in Hlen.
  assert (Hloop:
           forall (k: int),
             0 <= k <= length l / 2 ->
             SPEC (loop k)
               PRE(a ~> Array (
                       take k (LibList.rev l) ++
                         take (length l - k - k) (drop k l) ++
                         drop (length l - k) (LibList.rev l)
               ))
               POST(fun (_: unit) => a ~> Array (LibList.rev l))
         ). {
    intros k; induction_wf IH: (upto ((length l) / 2)) k.
    intros Hk.
    apply Hloop_spec; clear Hloop_spec.
    rewrite !Z.quot_div_nonneg in * |- *; try math.
    xif.
    + intros Hlt.
      assert (Hgt0: 0 < length l / 2) by math.
      pose proof (Hlenl := list_half_prop _ Hgt0).
      pose proof (Hklt := list_half_gt _ Hlenl).
      pose proof (Hhalf:= list_half_diag_leq l).
      pose proof (Hhalfle:= list_half_le l).
      assert (IA: Inhab A). {
          assert (0 <= length l / 2) by (apply Z_div_nonneg_nonneg; math).
          assert (Hlengt0: 0 < length l) by math; gen Hlengt0.
          destruct l; try (rewrite length_nil; math).
          intros _; apply Inhab_of_val; auto.
      }
      xapp. {
        apply int_index_prove; try math.
        rewrite <- length_eq; rew_list; rewrite length_take_nonneg; try (rewrite length_rev; math).
        rewrite length_drop_nonneg; try (rewrite length_rev; math); rewrite length_rev.
        rewrite length_take_nonneg; try (rewrite length_rev, length_drop_nonneg; math); try math.
        rewrite length_drop_nonneg; try math; split; try math.
      }
      xapp. {
        apply int_index_prove; try math.
        rewrite <- length_eq; rew_list; rewrite length_take_nonneg; try (rewrite length_rev; math).
        rewrite length_drop_nonneg; try (rewrite length_rev; math); rewrite length_rev.
        rewrite length_take_nonneg; try (rewrite length_rev, length_drop_nonneg; math); try math.
        rewrite length_drop_nonneg; try math; split; try math.
      }
      xapp. {
        apply int_index_prove; try math.
        rewrite <- length_eq; rew_list; rewrite length_take_nonneg; try (rewrite length_rev; math).
        rewrite length_drop_nonneg; try (rewrite length_rev; math); rewrite length_rev.
        rewrite length_take_nonneg; try (rewrite length_rev, length_drop_nonneg; math); try math.
        rewrite length_drop_nonneg; try math; split; try math.
      }
      xapp. {
        apply int_index_prove; try math.
        rewrite Plast.
        rewrite <- length_eq, length_update; rew_list; rewrite length_take_nonneg; try (rewrite length_rev; math).
        rewrite length_drop_nonneg; try (rewrite length_rev; math); rewrite length_rev.
        rewrite length_take_nonneg; try (rewrite length_rev, length_drop_nonneg; math); try math.
        rewrite length_drop_nonneg; try math; split; try math.
      }
      xapp (IH (k + 1)); try (apply upto_intro; math); try math; try xsimpl*.
      rewrite Plast.
      rewrite read_app, If_r; rewrite length_take_nonneg; try math; try (rewrite length_rev; math).
      rewrite read_app, If_l; try (rewrite length_take_nonneg; try math; try (rewrite length_drop_nonneg; math)).
      rewrite read_app, If_r; rewrite length_take_nonneg; try math; try (rewrite length_rev; math).
      rewrite read_app, If_l; try (rewrite length_take_nonneg; try math; try (rewrite length_drop_nonneg; math)).
      erewrite (@update_app_r _ _ 0 _); eauto; try math;
        try (rewrite length_take_nonneg; try math; try (rewrite length_rev; math)).
      erewrite (@update_app_l _ _ 0 _); eauto;
        try (rewrite length_take_nonneg; try math; rewrite length_drop_nonneg; try math).
      erewrite (@update_app_r _ _ (length l - 2 * k - 1) _); eauto; try math;
        try (rewrite length_take_nonneg; try math; try (rewrite length_rev; math)).
      erewrite (@update_app_l _ _ _ _); eauto;
        try (rewrite length_update, length_take_nonneg; try math; rewrite length_drop_nonneg; try math).
      math_rewrite (length l - (k + 1) = length l - k - 1).
      math_rewrite ((length l - k) = length l - k - 1 + 1).
      math_rewrite ((length l - k - 1 + 1 - 1 - (k + 1)) = length l - 2 * k - 2).
      math_rewrite ((length l - k - 1 + 1 - 1) = length l - k - 1).
      math_rewrite ((length l - k - 1 + 1 - k) = length l - 2 * k).
      math_rewrite (length l - 1 - k - k = length l - 2 * k - 1).
      math_rewrite (k - k = 0).
      math_rewrite ((length l - k - 1 + 1) = length l - k).
      symmetry.
      apply (eq_of_extens IA).
      * rew_list.
        rewrite length_take_nonneg, !length_update; try (rewrite length_rev; math).
        rewrite length_take_nonneg; [|rewrite length_drop_nonneg; try math].
        rewrite length_take_nonneg; [|rewrite length_rev; try math].
        rewrite length_take_nonneg; [|rewrite length_drop_nonneg; try math].
        do 2 (rewrite length_drop_nonneg; [|rewrite length_rev; try math]).
        rewrite length_rev; math.
      * intros i.
        rewrite index_eq_index_length, int_index_eq.
        rew_list.
        rewrite length_take_nonneg; try (rewrite length_rev; math).
        rewrite length_take_nonneg; [|rewrite length_drop_nonneg; math].
        rewrite length_drop_nonneg; [|rewrite length_rev; try math].
        rewrite length_rev.
        math_rewrite (k + 1 + (length l - 2 * k - 2 + (length l - (length l - k - 1))) = length l).
        intros Hi.
        case (Z.ltb_spec0 i k); rewrite <- lt_zarith; intros Hilt.
        ** rewrite read_app, If_l;
             try (rewrite length_take_nonneg; try (rewrite length_rev; math); try math).
           rewrite read_app, If_l;
             try (rewrite length_take_nonneg; try (rewrite length_rev; math); try math).
           rewrite read_take; try (rewrite length_rev; math); try (apply int_index_prove; math).
           rewrite read_take; try (rewrite length_rev; math); try (apply int_index_prove; math).
           auto.
        ** case (Z.ltb_spec0 i (k + 1)); rewrite <- lt_zarith; intros Hiltk.
           *** assert (Hik: i = k) by math; rewrite Hik.
               rewrite read_app, If_l;
                 try (rewrite length_take_nonneg; try (rewrite length_rev; math); try math).
               rewrite read_app, If_r;
                 try (rewrite length_take_nonneg; try (rewrite length_rev; math); try math).
               rewrite read_app, If_l; [| rewrite !length_update, length_take_nonneg; try (rewrite length_drop; math); math].
               math_rewrite (k - k = 0).
               rewrite read_update_neq; [ | apply int_index_prove; try (rewrite <- length_eq, length_update, length_take_nonneg; try (rewrite length_drop; math); math; math) | math ]; try math.
               rewrite read_update_same; [ try math  | apply int_index_prove; try (rewrite <- length_eq, length_take_nonneg; try (rewrite length_drop; math)); try math].
               rewrite read_take; try (rewrite length_rev; math); try (apply int_index_prove; math).
               rewrite read_take; [ | rewrite length_drop; try math | apply int_index_prove; try math ].
               rewrite read_rev; try (rewrite length_rev; math).
               rewrite rev_rev, length_rev.
               rewrite read_drop; [ | math | apply int_index_prove; try math ].
               f_equal; math.
           *** assert (Hik: i >= k + 1) by math.
               rewrite read_app, If_r;
                 try (rewrite length_take_nonneg; try (rewrite length_rev; math); try math).
               case (Z.ltb_spec0 i (length l - k - 1)); rewrite <- lt_zarith; intros Hltklen.
               **** rewrite read_app, If_l; [| rewrite length_take_nonneg; try (rewrite length_drop_nonneg; math); math ].
                    rewrite read_take; [|rewrite length_drop_nonneg; try math|apply int_index_prove; math ].
                    rewrite read_drop; try math; try (apply int_index_prove; math).
                    math_rewrite (k + 1 + (i - (k + 1)) = i).
                    rewrite read_app, If_r; rewrite length_take_nonneg; try math; try rewrite length_rev; try math.
                    rewrite read_app, If_l; try (rewrite !length_update, length_take_nonneg;try math; try rewrite length_drop_nonneg; try math).
                    rewrite read_update_neq; [ | apply int_index_prove; try math; rewrite <- length_eq, length_update, length_take_nonneg; try (rewrite length_drop; math); try math | math ].
                    rewrite read_update_neq; [ | apply int_index_prove; try math; rewrite <- length_eq, length_take_nonneg; try (rewrite length_drop; math); try math | math ].
                    rewrite read_take; [|rewrite length_drop_nonneg; math| apply int_index_prove; math].
                    rewrite read_drop; try (f_equal; math).
                    apply int_index_prove; math.
               **** rewrite read_app, If_r; [| rewrite length_take_nonneg; try (rewrite length_drop_nonneg; math); math ].
                    rewrite length_take_nonneg; try (rewrite length_drop; math).
                    rewrite read_drop; [ | rewrite length_rev; math | apply int_index_prove; try math; rewrite length_rev; try math ].
                    math_rewrite (length l - k - 1 + (i - (k + 1) - (length l - 2 * k - 2)) = i).
                    rewrite read_app, If_r; try (rewrite length_take_nonneg; try (rewrite length_rev; math); math).
                    rewrite length_take_nonneg; try (rewrite length_rev; math).
                    rewrite read_app.
                    rewrite !length_update, length_take_nonneg; try (rewrite length_drop_nonneg; math).
                    case (Z.ltb_spec0 (i - k) (length l - 2 * k)); rewrite <- lt_zarith; intros Hltkcase3.
                    rewrite If_l; auto.
                    ***** case (Z.eqb_spec (i - k) (length l - 2 * k - 1)); intros Heq.
                    assert (Hi_eq_k: i = length l - k - 1) by math.
                    rewrite Heq; rewrite read_update_same; [|apply int_index_prove; [ math | rewrite <- length_eq, length_update, length_take_nonneg; try (rewrite length_drop_nonneg; math); math ]].
                    rewrite read_take; [| rewrite length_drop; math | apply int_index_prove; math].
                    rewrite read_drop; [| math | apply int_index_prove; math].
                    rewrite read_rev; rewrite length_rev; try math.
                    rewrite rev_rev; f_equal; math.
                    rewrite read_update_neq; [|apply int_index_prove; math|math].
                    rewrite read_update_neq; [|apply int_index_prove; math|math].
                    rewrite read_take; [| rewrite length_drop; math | apply int_index_prove; math].
                    rewrite read_drop; [| math | apply int_index_prove; math].
                    rewrite read_rev; rewrite length_rev; try math.
                    ***** rewrite If_r; auto.
                    rewrite read_drop; try (f_equal; math); try (rewrite length_rev; math).
                    apply int_index_prove; try rewrite length_rev; try math.
    + intros Hlt; assert (Heq: k = length l / 2) by math; rewrite Heq.
      xvals*.
      math_rewrite ((length l - length l / 2 - length l / 2) = (if Z.odd (length l) then 1 else 0)).
      math_rewrite ((length l - length l / 2) = (length l / 2 + (if Z.odd (length l) then 1 else 0))).
      case_eq (Z.odd (length l));=> Hodd.
      * rewrite Hodd in Hlen.
        assert (IA: Inhab A). {
          assert (0 <= length l / 2) by (apply Z_div_nonneg_nonneg; math).
          assert (Hlengt0: 0 < length l) by math; gen Hlengt0.
          destruct l; try (rewrite length_nil; math).
          intros _; apply Inhab_of_val; auto.
        }
        rewrite (@take_pos_last _ IA _ 1);
          try (apply int_index_prove; try math;
               rewrite <- length_eq, length_drop_nonneg; math).
        math_rewrite (1 - 1 = 0).
        rewrite take_zero, app_nil_l, app_cons_one_r.
        rewrite read_drop; try math; try (apply int_index_prove; math).
        math_rewrite (length l / 2 + 0 = length l / 2).
        rewrite <- app_last_l.
        rewrite list_odd_index, Hodd; try math.
        math_rewrite (length l / 2 + 0 = length l / 2).
        math_rewrite ((length l / 2) = (length l / 2 + 1) - 1).
        rewrite <- take_pos_last;
          try (apply int_index_prove; rewrite <- ?length_eq, ?length_rev; math).
        math_rewrite ((length l / 2 + 1 - 1 + 1) = (length l / 2 + 1)).
        rewrite list_eq_take_app_drop; auto.
        rewrite <- ?length_eq, ?length_rev; math.
      * rewrite Z.add_0_r. rew_list.
        apply list_eq_take_app_drop; rew_list.
        rewrite Hlen at 2; rewrite Hodd; try math.
  }
  xapp*.
  - split; try math.
    pose proof (Hnonneg:= length_nonneg l).
    apply Z_div_nonneg_nonneg; math.
  - rewrite take_zero, drop_zero, app_nil_l.
    do 2 math_rewrite ((length l - 0) = length l).
    rewrite take_full_length, <- length_rev, drop_at_length, app_nil_r; auto.
  - xsimpl*.
Qed.
