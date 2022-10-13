Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.
From Common Require Import Verify_opt.

From Common Require Import Tactics.
From Common Require Import Utils.

From ProofsFindMapi Require Import Find_mapi_new_ml.


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
  (* xcf. *)
  (* xapp Array_proof.length_spec. *)
  (* xif as Hcond. *)
  (* - xvals*. { *)
  (*     apply length_zero_inv in Hcond; rewrite Hcond; simpl; auto. *)
  (*   } *)
  (* - xref value_found. *)
  (*   xletopaque tmp Htmp. *)
  (*   xapp (while_upto_spec 0 (length l) tmp (fun (i: credits) (res: bool) => *)
  (*              a ~> Array l \* *)
  (*              value_found ~~> list_find_mapi_internal 0 fp (take i l) \* *)
  (*              \[res = negb (is_some (list_find_mapi fp (take i l)))] *)
  (*         ) *)
  (*      ). { *)
  (*   intros i Hlen; apply Htmp; clear Htmp. *)
  (*   assert (IA: Inhab A). { *)
  (*     apply Inhab_of_val; destruct l; rew_list in Hlen; auto; try math. *)
  (*   } *)
  (*   xpullpure Hfm. *)
  (*   xapp. { apply int_index_prove; math. } *)
  (*   xapp (H i l[i]); xsimpl*. *)
  (*   xapp opt_is_some_spec. *)
  (*   xif; intros Hf_eq. *)
  (*   - xapp. *)
  (*     xlet. *)
  (*     xvals*; rewrite find_mapi_unfold in *. *)
  (*     rewrite (take_pos_last IA); [ | apply int_index_prove; math ]. *)
  (*     math_rewrite ((i + 1 - 1) = i). *)
  (*     rewrite find_mapi_app_r; *)
  (*       [ | destruct (list_find_mapi fp (take i l)); simpl in Hfm; try inversion Hfm; auto ]. *)
  (*     rewrite length_take_nonneg; try math. *)
  (*   math_rewrite (0 + i = i). *)
  (*   simpl; case (fp i l[i]); auto. *)
  (*     rewrite (take_pos_last IA); [ | apply int_index_prove; try math ]. *)
  (*     math_rewrite ((i + 1 - 1) = i). *)
  (*     rewrite find_mapi_app_r; *)
  (*       [ | destruct (list_find_mapi 0 fp (take i l)); simpl in Hfm; try inversion Hfm; auto ]. *)
  (*     rewrite length_take_nonneg; try math. *)
  (*     math_rewrite (0 + i = i). *)
  (*   simpl; gen Pres; case (fp i l[i]); simpl; auto. *)
  (*   - xvals. *)
  (*     xlet. *)
  (*     xvals*; auto. *)
  (*     rewrite (take_pos_last IA (i + 1)); [ | apply int_index_prove; math ]. *)
  (*     math_rewrite ((i + 1 - 1) = i). *)
  (*     rewrite find_mapi_app_r; *)
  (*       [ | destruct (list_find_mapi 0 fp (take i l)); simpl in Hfm; try inversion Hfm; auto ]. *)
  (*     rewrite length_take_nonneg; try math. *)
  (*   math_rewrite (0 + i = i). *)
  (*   simpl. destruct (fp i l[i]); simpl in Hf_eq; auto; [(contradiction Hf_eq; auto)|]. *)
  (*   simpl in Pres. *)
  (*   apply (f_equal negb) in Hfm; rewrite Bool.negb_involutive in Hfm; simpl in Hfm. *)
  (*   symmetry in Hfm. *)
  (*   apply not_is_some_eq in Hfm; rewrite Hfm; auto. *)
  (*   rewrite (take_pos_last IA); [ | apply int_index_prove; math ]. *)
  (*   math_rewrite ((i + 1 - 1) = i). *)
  (*   rewrite find_mapi_app_r; *)
  (*       [ | destruct (list_find_mapi 0 fp (take i l)); simpl in Hfm; try inversion Hfm; auto ]. *)
  (*     rewrite length_take_nonneg; try math. *)
  (*     math_rewrite (0 + i = i). *)
  (*     rewrite find_mapi_singleton. *)
  (*     rewrite negb_eq_neg; auto. *)
  (* } { math. } { rewrite take_zero; simpl; auto. } *)
  (* intros res i [Hi Himpl] Heq. *)
  (* xmatch; xapp*. xsimpl*. { *)
  (*   apply (f_equal negb) in Heq; rewrite Bool.negb_involutive in Heq; simpl in Heq. *)
  (*   symmetry in Heq. *)
  (*   destruct res; simpl in Himpl, Heq. *)
  (*   - apply not_is_some_eq in Heq. *)
  (*     assert (Heqi: i = length l) by (apply Z.eqb_eq; auto). *)
  (*     rewrite Heqi in *. *)
  (*     rewrite take_full_length in *. *)
  (*     auto. *)
  (*   - apply is_some_ex in Heq as [res Heq]. *)
  (*     symmetry; rewrite Heq. *)
  (*     rewrite <- (@list_eq_take_app_drop _ i l) at 1; try math. *)
  (*     rewrite find_mapi_app_l; auto. *)
  (*     rewrite Heq; simpl; auto. *)
  (* } *)
Admitted.

