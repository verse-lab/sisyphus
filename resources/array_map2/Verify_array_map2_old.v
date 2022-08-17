Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayMap2 Require Import Verify_array_map2_utils.
From ProofsArrayMap2 Require Import array_map2_old_ml.


Lemma to_array_spec :
  forall (A B C: Type) `{EA:Enc A} `{EB: Enc B} `{EC: Enc C}
         (f: func) (a_xs a_ys: loc)
         (xs:list A) (ys: list B)
         (fp: A -> B -> C),
    (forall (a: A) (b: B), SPEC_PURE (f a b) POST (fun (c: C) => \[c = fp a b])) ->
 SPEC (array_map2 f a_xs a_ys)
   PRE (\[ length xs = length ys /\ length xs > 0])
   INV (a_xs ~> Array xs \* a_ys ~> Array ys)
   POST (fun (res: loc) => res ~> Array (map2 fp xs ys)).
Proof using.
  intros A B C EA EB EC f a_xs a_ys xs ys fp Hfp.
  xcf.
  xpull;=> [Hlen Hgt0].
  xapp.
  xapp.
  xif;=> Hprop; [(rewrite Px0__ in Hprop; rewrite istrue_isTrue_eq in Hprop; contradiction Hprop)|].
  clear x0__ Px0__ Hprop.
  xvals.
  assert (IA: Inhab A). {
    gen Hgt0.
    destruct xs; try (rewrite length_nil; math).
        intros _; apply Inhab_of_val; auto.
  }
  assert (IB: Inhab B). {
    assert (Hgtb0: length ys > 0) by math; gen Hgtb0.
    destruct ys; try (rewrite length_nil; math).
        intros _; apply Inhab_of_val; auto.
  }
  assert (IC: Inhab C). {
    apply Inhab_of_val.
    apply fp; apply arbitrary.
  }
  xapp; [apply int_index_prove; try math |].
  xapp; [apply int_index_prove; try math |].
  xapp (Hfp xs[0] ys[0]).
  xapp; [try math|]; intros res data Hdata.
  xlet as;=> loop Hloop_spec.
  assert (Hloop:
           forall (i: int), 0 <= i <= length xs ->
             SPEC (loop i)
               PRE (res ~> Array (
                        take i (map2 fp xs ys) ++
                          drop i (make (length xs) (fp xs[0] ys[0]))))
               INV (a_xs ~> Array xs \* a_ys ~> Array ys)
               POST (fun (_: unit) => res ~> Array ((map2 fp xs ys)))
         ). {
    intros i; induction_wf IH: (upto (length xs)) i.
    intros Hi.
    apply Hloop_spec; clear Hloop_spec.
    xif.
    - intros Hlt.
      xapp; try (apply int_index_prove; math).
      xapp; try (apply int_index_prove; math).
      xapp (Hfp).
      xapp; 
        try (apply int_index_prove; try math;
        rewrite <- length_eq, length_app, length_take_nonneg,
        length_drop_nonneg, length_make;
        rewrite ?length_make, ?length_map2_l;
             math).
      xapp; try math; try (apply upto_intro; math). {
        rewrite !drop_make; try math.
        erewrite (@update_app_r _ _ 0); eauto; try math;
          try (rewrite length_take_nonneg; rewrite ?length_map2_l; math).
        rewrite make_eq_cons_make_pred; try math;
          rewrite update_zero, <- app_last_l.
        f_equal; try (f_equal; math).
        rewrite <- (@map2_index _ _ _ _ _ IC); try math.
        math_rewrite (i = (i + 1) - 1).
        rewrite <- take_pos_last;
          try (apply index_of_index_length; apply int_index_prove;
               rewrite ?length_map2_l; math).
        f_equal; math.
      }
      xsimpl*.
    - intros Hnlt. assert (Hi_eq: i = length xs) by math.
      xvals*.
      rewrite Hi_eq.
      rewrite <- (length_map2_l fp xs ys) at 1; try math.
      rewrite take_full_length.
      rewrite <- (@length_make _ (length xs) (fp xs[0] ys[0])) at 1; try math.
      rewrite drop_at_length.
      rewrite app_nil_r; auto.
  }
  xapp; try math;
    try (rewrite take_zero, drop_zero, app_nil_l; auto).
  xvals*.
Qed.
