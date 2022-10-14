Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver Verify_opt.

From ProofsArrayExists Require Import Array_exists_new_ml.


Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = List.existsb fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec 0 (length l) tmp
          (fun (i: int) (b: option bool) =>
             \[is_some b = List.existsb fp (take i l)] \*
               a ~> Array l)
       ). {
    sis_solve_start.
    rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
    math_rewrite ((i + 1 - 1) = i).
    rewrite list_existsb_app; simpl; rewrite H1; simpl; rewrite istrue_or_eq; auto. 
    rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
    math_rewrite ((i + 1 - 1) = i).
    rewrite list_existsb_app; simpl; rewrite !istrue_or_eq, !not_or_eq; split;
      rewrite ?Bool.orb_false_r; auto.
    rewrite <- H0; simpl; auto.
  }
  { math. }
  { rewrite take_zero; simpl; auto. }
  intros fin i_b Hres Hexists.
  xapp (opt_is_some_spec).
  xvals*. {
    destruct fin; destruct Hres as [Hlen Himpl]; simpl in *.
    - rewrite <- (@list_eq_take_app_drop _ i_b l) at 1; try math.
      rewrite list_existsb_app; rewrite <- Hexists; simpl; auto.
    - assert (Heq: i_b = length l) by (apply Z.eqb_eq; auto).
      rewrite Heq, take_full_length in Hexists; auto.
  }
Qed.
