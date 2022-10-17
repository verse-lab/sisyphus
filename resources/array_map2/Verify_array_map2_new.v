Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators Verify_arr Verify_list.

From Common Require Import Tactics Utils Solver.

From ProofsArrayMap2 Require Import Array_map2_new_ml.

Lemma array_map2_spec :
  forall (A : Type) `{EA : Enc A}  (B : Type) `{EB : Enc B}
         (C : Type) `{EC : Enc C}
         (f: func) (xs: array A) (ys: array B)
         (lx: list A) (ly: list B)
         (fp: A -> B -> C),
    (forall (a: A) (b: B),
        SPEC_PURE (f a b)
          POST (fun (c: C) => \[c = fp a b])) ->
    (length lx = length ly) ->
  SPEC (array_map2 f xs ys)
  PRE (xs ~> Array lx \* ys ~> Array ly)
  POST (fun (cs : array C) => xs ~> Array lx \* ys ~> Array ly \*
                                cs ~> Array (map2 fp (combine lx ly))).
Proof using (All).
  xcf.
  xapp.
  xif as cond.
  - xvalemptyarr. { repeat sis_list_solver. }
  - xinhab_inner A.
    xinhab_inner B.
    xapp. { sis_handle_int_index_prove. }
    xapp. { sis_handle_int_index_prove. }
    xapp.
    xalloc cs data Hdata.
    xapp (array_to_list_spec xs).
    xapp (array_to_list_spec ys).
    xapp (list_combine_spec). { auto. }
    xletopaque tmp Htmp.
    xapp (list_ml_iteri_spec tmp (combine lx ly)
            (fun (t: list (A * B)) =>
               ys ~> Array ly \*
               xs ~> Array lx \*
               cs ~> Array (map2 fp t ++ drop (length t) data)
         )). {
      sis_solve_start.
      sis_handle_int_index_prove.
      assert (length lx = length (combine lx ly)). {
        rewrite !length_eq, length_combine; auto; math.
      }
      unfold map2; subst; rewrite length_map, length_drop_nonneg;
        rewrite length_make; rewrite H1, Heq; rew_list; math.
      assert (Hi_eq: i = length (map2 fp t)). {
        unfold map2; subst; rewrite length_map; auto.
      }
      rewrite Hi_eq.
      sis_handle_list_update.
      unfold map2; rewrite map_last; rew_list; f_equal.
      destruct x as [lft rgt]; simpl.
      assert (length lx = length (combine lx ly)). {
        rewrite !length_eq, length_combine; auto; math.
      }
      rewrite drop_update_zero; auto; subst; rewrite length_make; try math.
      rewrite H1, Heq; rew_list; math.
    }
    xmatch.
    xvals*. {
      subst.
      assert (length lx = length (combine lx ly)). {
        rewrite !length_eq, length_combine; auto; math.
      }
      rewrite H1.
      sis_handle_take_drop_full_length; rew_list; auto.
    }
Qed.

