Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsArrayMap2 Require Import Array_map2_old_ml.

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
  - xinhab.
    xapp. { sis_handle_int_index_prove. }
    xinhab_inner A.
    xapp.  { sis_handle_int_index_prove. }
    xapp.
    xalloc cs data Hdata.
    xletopaque tmp Htmp.
    xapp (for_upto_spec 0 (length lx) tmp
            (fun (i: int) =>
               xs ~> Array lx \*
               ys ~> Array ly \*
               cs ~> Array (
                 take i (map2 fp (combine lx ly))
                ++ drop i (make (length lx) (fp lx[0] ly[0]))
               )
            )
         ). {
      sis_solve_start.
      sis_handle_int_index_prove.
      unfold map2.
      rewrite length_take_nonneg; rew_list;
      try (rewrite length_map, length_eq, length_combine, <- length_eq; math).
      rewrite length_drop_nonneg; rew_list; try (rewrite length_make; math).
      sis_handle_take_splitting_goals;
      try (rewrite length_take_nonneg; auto; unfold map2;
           rewrite length_map, length_eq, length_combine, <- length_eq; math).
      rewrite (@take_pos_last _ (Inhab_of_val (fp lx[0] ly[0]))
                 (map2 fp (combine lx ly)) (i + 1));
      try (sis_handle_int_index_prove;
        unfold map2; rewrite length_map, length_eq, length_combine, <- length_eq; math).
      math_rewrite (i + 1 - 1 = i); rew_list.
      f_equal.
      rewrite (@read_map2_combine _ IA0 _ IA); auto.
      rewrite drop_make_eq; try math.
      rewrite drop_make_eq; try math.
      math_rewrite (length lx - i = length lx - (i + 1) + 1).
      rewrite make_succ_l; try math.
      rewrite update_zero; auto.
    }
    { math. } { rewrite take_zero; simpl; auto. }
  xmatch.
  xvals*. { repeat sis_handle_take_drop_full_length; rew_list; auto. }
Qed.
