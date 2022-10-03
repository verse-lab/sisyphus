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

(* evar (symbol_4: A). *)
(* evar ( symbol_5: A). *)
(* evar (symbol_6: A). *)
(* evar (B: Type). *)
(* evar (init: B). *)
(* evar (I_fold: list A -> B -> hprop). *)
(* evar (Hf_fold: (forall (acc : B) (v : A) (t r : list A), *)
(*         symbol_4 :: symbol_5 :: symbol_6 :: nil = t ++ v :: r -> *)
(*         SPEC (tmp acc v) *)
(*         PRE I_fold t acc *)
(*         POST (fun acc0 : B => I_fold (t & v) acc0))). *)
(* (* print_reduced (list_fold_spec *) *)
(* (*                  tmp init (symbol_4 :: symbol_5 :: symbol_6 :: nil) I_fold Hf_fold). *) *)
(* evar (I: list A -> hprop). *)
(* evar (HF: (forall (i : credits) (x : A) (t r : list A) , *)
(*         symbol_4 :: symbol_5 :: symbol_6 :: nil = t ++ x :: r -> *)
(*         i = length t -> SPEC (tmp i x) *)
(*                         PRE I t *)
(*                         POSTUNIT I (t & x))). *)

(* print_reduced (list_ml_iteri_spec *)
(*                  (tmp: val) (symbol_4 :: symbol_5 :: symbol_6 :: nil) *)
(*                  I HF). *)

(* print_reduced (@list_iteri_aux_spec _ _ tmp 0  *)
(*                  (symbol_4 :: symbol_5 :: symbol_6 :: nil) nil (symbol_4 :: symbol_5 :: symbol_6 :: nil) I HF). *)
Admitted.
