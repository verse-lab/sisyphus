Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFindMap Require Import Verify_array_find_map_utils.
From ProofsArrayFindMap Require Import array_find_map_old_ml.

Lemma to_array_spec :
  forall A (B: Type) `{EA:Enc A} `{EB: Enc B} (a:loc) (f: func)
         (l:list A) (fp: A -> option B),
    (forall (a: A), SPEC_PURE (f a) POST (fun (b: option B) => \[b = fp a])) ->
 SPEC (find_map a f)
    PRE (a ~> Array l)
    POST (fun (res: option B) => \[res = list_find_map fp l] \* a ~> Array l).
Proof using.
  intros A B EA EB a f l fp Hfp.
  xcf.
  xlet.
  assert (Hfindi:
           forall
             (i: int) (len: int)
             (Hi: 0 <= i)
            (Hlen: len = length l)
            (Hfind: list_find_map fp (take i l) = None),
            SPEC (find_map_loop a f len i)
              PRE(a ~> Array l)
              POST(fun (res: option B) =>
                     \[res = list_find_map fp l] \* a ~> Array l)). {
    intros i.
    induction_wf IHi: (upto (length l)) i.
    intros len Hi Hlen Hfind.
    eapply Spec_find_map_loop; clear Spec_find_map_loop.
    xif;=> Hif.
    - xval*; rewrite take_ge in Hfind; [| rewrite Hlen in Hif; auto]; rewrite Hfind; xsimpl*.
    - assert (IA: Inhab A). {
        assert (Hlengt0: 0 < len) by math; gen Hlengt0.
        rewrite Hlen; destruct l; try (rewrite length_nil; math).
        intros _; apply Inhab_of_val; auto.
      }
      xapp; [apply int_index_prove; math |].
      xapp (Hfp l[i]).
      xmatch.
      * xapp (IHi); try math.
        + apply upto_intro; try math.
        + erewrite take_pos_last; try (apply int_index_prove; math).
          eapply length_find_propagate; math_rewrite ((i + 1 - 1) = i); auto.
        + xsimpl*.
      * xvals*.
        erewrite length_find_final; eauto.
        rewrite <- (@list_eq_take_app_drop _ i l) at 1; try math.
        f_equal.
        rewrite  (@index_cons A IA (drop i l)) at 1; eauto;
          try (rewrite length_drop_nonneg; math).
        rewrite read_drop; try math; try (apply int_index_prove; math).
        math_rewrite (i + 0 = i); f_equal.
  }
  xapp length_spec.
  xapp Hfindi; try math; try (rewrite take_zero; simpl; auto).
  xsimpl*.
Qed.
