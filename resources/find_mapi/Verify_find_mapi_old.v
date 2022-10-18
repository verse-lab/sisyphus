Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics.
From Common Require Import Utils.

From ProofsFindMapi Require Import Find_mapi_old_ml.

Lemma find_mapi_spec :
  forall (A : Type) `{EA : Enc A}  (B : Type) `{EB : Enc B}
         (a: array A) (f: func) (l: list A) (fp: credits -> A -> option B),
    (forall (i: int) (a: A),
        SPEC_PURE (f i a)
          POST (fun (b: option B) => \[b = fp i a])) ->
  SPEC (find_mapi a f)
  PRE (a ~> Array l)
  POST (fun (b : option B) => \[ b = list_find_mapi fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec B 0 (length l) tmp (fun (i: credits) (res: option B) =>
               a ~> Array l \* \[res = list_find_mapi fp (take i l)]
          )
       ). {
    intros i Hlen; apply Htmp; clear Htmp.
    assert (IA: Inhab A). {
      apply Inhab_of_val; destruct l; rew_list in Hlen; auto; try math.
    }
    xpullpure Hfm.
    xapp. { apply int_index_prove; math. }
    xapp (H i l[i]); xsimpl*.
    rewrite (take_pos_last IA); [ | apply int_index_prove; math ].
    math_rewrite ((i + 1 - 1) = i).
    rewrite find_mapi_unfold.
    rewrite find_mapi_app_r; auto.
    rewrite length_take_nonneg; try math.
    math_rewrite (0 + i = i).
    simpl; case (fp i l[i]); auto.
  } { math. } { rewrite take_zero; simpl; auto. }
  intros res i [Hi Himpl] Heq.
  xvals*. {
    destruct res as [ res_vl|]; simpl in Himpl.
    - rewrite <- (@list_eq_take_app_drop _ i l); try math.
      rewrite find_mapi_unfold, find_mapi_app_l in *; auto.
      rewrite <- Heq; simpl; auto.
    - assert (Heqi: i = length l) by (apply Z.eqb_eq; auto).
      rewrite Heqi in Heq.
      rewrite take_full_length in Heq.
      auto.
  }
Qed.
