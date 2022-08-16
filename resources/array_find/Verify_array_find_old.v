Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFind Require Import Verify_array_find_utils.
From ProofsArrayFind Require Import array_find_old_ml.


Lemma to_array_spec :
  forall A `{EA:Enc A} (a:loc) (f: func)
         (l:list A) (fp: int -> A -> bool),
    (forall (i: int) (a: A), SPEC_PURE (f i a) POST (fun (b: bool) => \[b = fp i a])) ->
 SPEC (findi a f)
    PRE (a ~> Array l)
    POST (fun (res: option (int * A)) => \[res = list_findi fp 0 l] \* a ~> Array l).
Proof using.
  intros A EA a f l fp Hfp.
  xcf.
  xlet.
  assert (Hfindi: forall (i: int) (len: int)
            (Hi: 0 <= i)
            (Hlen: len = length l)
            (Hfind: list_findi fp 0 (take i l) = None),
            SPEC (findi_loop a f len i)
              PRE(a ~> Array l)
              POST(fun (res: option (int * A)) =>
                     \[res = list_findi fp 0 l] \* a ~> Array l)). {
    intros i.
    induction_wf IHi: (upto (length l)) i.
    intros len Hi Hlen Hfind.
    eapply Spec_findi_loop; clear Spec_findi_loop.
    xif;=> Hif.
    - xval*; rewrite take_ge in Hfind; [| rewrite Hlen in Hif; auto]; rewrite Hfind; xsimpl*.
    - assert (IA: Inhab A). {
        assert (Hlengt0: 0 < len) by math; gen Hlengt0.
        rewrite Hlen; destruct l; try (rewrite length_nil; math).
        intros _; apply Inhab_of_val; auto.
      }
      xapp; [apply int_index_prove; math |].
      xapp (Hfp i l[i]).
      xif;=> Hfpvl.
      * xapp; [apply int_index_prove; math | ].
        xval*.
        xsimpl*.
        {
          assert (Hi_len: i = length (take i l))
            by (rewrite length_take_nonneg; auto; math).
          rewrite Hi_len at 1.
          erewrite length_find_final; eauto; try (rewrite <- Hi_len; auto).
          rewrite <- (@list_eq_take_app_drop _ i l) at 1; try math.
          apply f_equal.
          math_rewrite (i = i + 0);
            rewrite <- read_drop; try math; try (apply int_index_prove; math);
          math_rewrite (i + 0 = i).
          rewrite  (@index_cons A IA (drop i l)) at 1; eauto.
          rewrite length_drop_nonneg; try math.
        }
      * xapp (IHi); try math.
        + apply upto_intro; try math.
        + erewrite take_pos_last; try (apply int_index_prove; math).
          eapply length_find_propagate; math_rewrite ((i + 1 - 1) = i); auto.
          rewrite length_take_nonneg; try math; auto.
          destruct (fp i l[i]); auto.
          contradiction Hfpvl; auto.
        + xsimpl*.
  }
  xapp length_spec.
  xapp Hfindi; try math; try (rewrite take_zero; simpl; auto).
  xsimpl*.
Qed.
