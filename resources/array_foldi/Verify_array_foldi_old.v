Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFoldi Require Import Verify_array_foldi_utils.
From ProofsArrayFoldi Require Import array_foldi_old_ml.

Lemma to_array_spec :
  forall A (B: Type) `{EA:Enc A} `{EB: Enc B}
         (a: loc) (init: B) (f: func)
         (l:list A) (fp: int -> B -> A -> B),
    (forall (i: int) (acc: B) (vl: A),
        SPEC_PURE (f i acc vl)
        POST (fun (b: B) => \[b = fp i acc vl])) ->
 SPEC (foldi a init f)
    PRE (a ~> Array l)
    POST (fun (res: B) => \[res = foldi_pure fp 0 init l] \* a ~> Array l).
Proof using.
  intros A B EA EB a init f l fp Hfp.
  xcf.
  xlet as; => foldi Hfoldi.
  assert
    (Hfoldi_spec:
      forall (i: int) (acc: B),
      0 <= i <= length l ->
      SPEC (foldi a i acc f)
      PRE (\[acc = foldi_pure fp 0 init (take i l)])
      INV (a ~> Array l)
      POST (fun (res: B) => \[res = foldi_pure fp 0 init l])
    ). {
    intros i; induction_wf IH: (upto (length l)) i.
    intros acc Hi.
    eapply Hfoldi; clear Hfoldi.
    xpull;=> Hfold.
    xapp (length_spec).
    xif;=> Hlen_eq.
    - rewrite Px1__ in Hlen_eq; apply (istrue_isTrue_forw (i = length l)) in Hlen_eq.
      xvals*.  {
        gen Hfold; rewrite Hlen_eq.
        rewrite !take_ge; try math. auto.
      }
    - rewrite Px1__ in Hlen_eq; rewrite <- istrue_neg_eq in Hlen_eq;
        rewrite <- isTrue_not in Hlen_eq; apply istrue_isTrue_forw in Hlen_eq.
      assert (IA: Inhab A). {
        assert (Hlengt0: 0 < length l) by math; gen Hlengt0.
        destruct l; try (rewrite length_nil; math).
        intros _; apply Inhab_of_val; auto.
      }
      xapp; try(apply int_index_prove; math).
      xapp (Hfp i acc).
      xapp (IH (i + 1)); try (apply upto_intro; try math); try math.
      + rewrite (take_pos_last IA); try (apply int_index_prove; math).
        math_rewrite (i + 1 - 1 = i).
        rewrite foldi_pure_last.
        rewrite length_take_nonneg; try math.
        f_equal; try math; auto.
      + xsimpl*.
  }
  xapp; try math; try (rewrite take_zero; simpl; auto).
  xsimpl*.
Qed.
