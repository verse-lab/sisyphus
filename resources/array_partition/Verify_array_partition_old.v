Set Implicit Arguments.
Generalizable Variable A EA.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_arr.
From Common Require Import Tactics Utils Solver.

From ProofsArrayPartition Require Import Array_partition_old_ml.

Lemma array_partition_spec :
  forall (A : Type) `{EA : Enc A} (p: func) (a: array A)
         (pp : A -> bool) (l: list A),
  (forall a: A,
      SPEC (p a)
      PRE (\[])
      POST (fun (b: bool) => \[b = pp a])
  ) ->
  SPEC (partition p a)
  PRE (a ~> Array l)
  POST (fun '((a_t, a_f) : (loc * loc)) =>
          a ~> Array l \*
          a_t ~> Array (filter pp l) \*
            a_f ~> Array (filter_not pp l)
  ).
Proof using (All).
  xcf.
  xapp.
  xif as Hcond.
  - xapp. intros a_t.
    xapp. intros a_f.
    xvals*. { sis_list_solver. }
    { sis_list_solver. }
  - xinhab.
    xapp. { auto. }
    xalloc a_t a_t_data Ha_t_data.
    xapp. { auto. }
    xalloc a_f a_f_data Ha_f_data.
    xref c_t.
    xref c_f.
    xletopaque tmp Htmp.
    xapp (array_iter_spec tmp a l (fun (prefix: list A) =>
                                     c_t ~~> (length (filter pp prefix)) \*
                                       c_f ~~> (length (filter_not pp prefix)) \*
                                       a_t ~> Array (
                                         (filter pp prefix) ++ drop (length (filter pp prefix)) a_t_data
                                       ) \*
                                       a_f ~> Array (
                                         (filter_not pp prefix) ++ drop (length (filter_not pp prefix)) a_f_data
                                       )
            )
         ). {
      (* sis_solve_start; autorewrite with rew_list filter_lemmas;  *)
      (*   sis_handle_if; rew_list; auto;  *)
      (*   sis_handle_int_index_prove; *)
      (*   sis_expand_rewrites; *)
      (*   rew_list. *)
      (* sis_normalize_length; sis_dispatch_filter_goal. *)
      (* sis_normalize_length; sis_dispatch_filter_goal. *)
      (* sis_normalize_length; rew_list; sis_handle_list_update; f_equal. *)
      (* sis_normalize_succs. *)
      intros v t r Htvr; apply Htmp; clear Htmp.
      xapp (H).
      xif;=> Htmpcond.
      - xapp.
        xapp. {
          apply int_index_prove; [ apply length_nonneg; rew_list | ].
          rewrite <- length_eq; rew_list.
          pose proof (Hft:= length_filter t (fun x : A => pp x)).
          rewrite length_drop_nonneg, Ha_t_data, length_make, Htvr; rew_list; try math.
          rewrite Ha_t_data, Htvr, length_make; rew_list;  try math.
        }
        xmatch.
        xapp*.
        xsimpl*. {
          rewrite filter_last, Htmpcond, If_l; rew_list; auto; try math.
        } {
          rewrite filter_not_last, Htmpcond, If_l; rew_list; auto; try math.
        } {
          pose proof (Hft:= length_filter t (fun x : A => pp x)).
          rewrite (@update_app_r _ _ 0 _ (length (filter (fun x : A => pp x) t))); auto; try math.
          rewrite filter_last, Htmpcond, If_l; rew_list; auto.
          repeat f_equal.
          apply (eq_of_extens IA). {
            rew_list; rewrite length_update, !length_drop_nonneg, Ha_t_data, length_make; try math.
            rewrite Ha_t_data, length_make, Htvr; rew_list; try math.
            rewrite Ha_t_data, length_make, Htvr; rew_list; try math.
          } {
            intros i; rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Ha_t_data, length_make, Htvr; rew_list; try math.
            intros Hlen.
            case (Z.eqb_spec i 0);=> Hi0.
            - rewrite Hi0, read_update_same, read_zero; auto.
              apply int_index_prove; [math|].
              rewrite <- length_eq; rew_list; rewrite length_drop_nonneg; rewrite length_make; math.
            - rewrite read_update_neq; try math;
                try (apply int_index_prove; [math|];
                     rewrite <- length_eq; rew_list; rewrite length_drop_nonneg; rewrite length_make; math).
              rewrite read_cons_pos, !read_drop; rewrite ?length_make; try math; try (f_equal; math).
              apply int_index_prove; math.
              apply int_index_prove; math.
          }
        } {
          pose proof (Hft:= length_filter_not t (fun x : A => pp x)).
          rewrite filter_not_last, Htmpcond, If_l; rew_list; auto.
          repeat f_equal.
          math.
        }
      - xapp.
        xapp. {
          apply int_index_prove; [ apply length_nonneg; rew_list | ].
          rewrite <- length_eq; rew_list.
          pose proof (Hft:= length_filter_not t (fun x : A => pp x)).
          rewrite length_drop_nonneg, Ha_f_data, length_make, Htvr; rew_list; try math.
          rewrite Ha_f_data, Htvr, length_make; rew_list;  try math.
        }
        xmatch.
        xapp*.
        xsimpl*. {
          rewrite filter_last, If_r; rew_list; auto; try math.
        } {
          rewrite filter_not_last, If_r; rew_list; auto; try math.
        } {
          pose proof (Hft:= length_filter t (fun x : A => pp x)).
          rewrite filter_last, If_r; rew_list; auto.
          repeat f_equal.
          math.
        } {
          pose proof (Hft:= length_filter_not t (fun x : A => pp x)).
          rewrite (@update_app_r _ _ 0 _ (length (filter_not (fun x : A => pp x) t))); auto; try math.
          rewrite filter_not_last, If_r; rew_list; auto.
          repeat f_equal.
          apply (eq_of_extens IA). {
            rew_list; rewrite length_update, !length_drop_nonneg, Ha_f_data, length_make; try math.
            rewrite Ha_f_data, length_make, Htvr; rew_list; try math.
            rewrite Ha_f_data, length_make, Htvr; rew_list; try math.
          } {
            intros i; rewrite index_eq_index_length, int_index_eq.
            rewrite length_update, length_drop_nonneg; rewrite Ha_f_data, length_make, Htvr; rew_list; try math.
            intros Hlen.
            case (Z.eqb_spec i 0);=> Hi0.
            - rewrite Hi0, read_update_same, read_zero; auto.
              apply int_index_prove; [math|].
              rewrite <- length_eq; rew_list; rewrite length_drop_nonneg; rewrite length_make; math.
            - rewrite read_update_neq; try math;
                try (apply int_index_prove; [math|];
                     rewrite <- length_eq; rew_list; rewrite length_drop_nonneg; rewrite length_make; math).
              rewrite read_cons_pos, !read_drop; rewrite ?length_make; try math; try (f_equal; math).
              apply int_index_prove; math.
              apply int_index_prove; math.
          }
        }
    }
    xmatch.
    xapp.
    xapp. { apply length_nonneg. }
    intros a_left.
    xapp.
    xapp. { apply length_nonneg. }
    intros a_right.
    xvals*. {
      rewrite take_prefix_length; auto.
    } {
      rewrite take_prefix_length; auto.
    }
Qed.
