Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_new_ml.

(* Declare ML Module "proof_reduction". *)
(* Declare ML Module "printreduced". *)

Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
(* xcf. *)
(* case l as [ | x tl] eqn:H_eqn. *)
(* - xmatch. *)
(* xvalemptyarr. *)
(* - xmatch. *)
(* xletopaque len Hlen. *)
(* xalloc a data Hdata. *)
(* xletopaque tmp Htmp. *)

(* xapp (@list_ml_iteri_spec _ _ tmp (x :: tl) *)
(*         (fun (t: list A) => *)
(*            a ~> Array ((make (length l - (length t)) x) ++ (take (length t) (rev t))) *)
(*         ) *)
(*      ). { *)
(*   intros i v t r Htvr Hilen. *)
(*   apply Htmp; clear Htmp. *)
(*   xapp. { *)
(*     apply int_index_prove; [ *)
(*         rewrite Hlen, Htvr, Hilen; rew_list; math | *)
(*       ]. *)
(*     rewrite <- length_eq, length_app, length_make; *)
(*       rewrite ?H_eqn, Htvr; rew_list; try math. *)
(*     rewrite take_ge; rewrite length_rev; try math. *)
(*     rewrite Hlen, Htvr; rew_list; math. *)
(*   } { *)
(*     xsimpl*. *)
(*     rew_list. *)
(*     rewrite Hlen, H_eqn, Htvr, Hilen; rew_list. *)
(*     math_rewrite ( *)
(*         length t + (1 + length r) - 1 - length t = *)
(*           length r *)
(*       ). *)
(*     math_rewrite ( *)
(*         length t + (1 + length r) - length t = *)
(*           length r + 1 *)
(*       ). *)
(*     math_rewrite ((length t + (1 + length r) - (1 + length t)) = *)
(*                     length r *)
(*                  ). *)
(*     rewrite make_succ_r; [|math]. *)
(*     rewrite app_last_l, update_middle; rewrite ?length_make; try math. *)
(*     rewrite take_cons_pos; try math. *)
(*     rewrite app_last_l; repeat f_equal; try math. *)
(*   } *)
(* } *)
(* { *)
(*   rew_list; rewrite Hdata, Hlen, <- H_eqn; repeat f_equal; try math. *)
(* } *)
(* xmatch. *)
(* xvals*. { *)
(*   rewrite H_eqn; rew_list. *)
(*   math_rewrite ((1 + length tl - (1 + length tl)) = 0). *)
(*   rewrite make_zero, app_nil_l, take_ge; rew_list; auto; try math. *)
(* } *)
(* Qed. *)
Admitted.
