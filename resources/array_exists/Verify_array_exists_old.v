Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsArrayExists Require Import Array_exists_old_ml.

Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = existsb fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xref result.
  xletopaque tmp Htmp.
  xapp (while_upto_spec 0 (length l) tmp
           (fun (i: int) (b: bool) => \[b = negb (existsb fp (take i l))] \*
                         result ~~> (existsb fp (take i l)) \*
                         a ~> Array l)
       ). {
    sis_solve_start. {
      unfold existsb in *.
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      apply (f_equal negb) in H0; rewrite Bool.negb_involutive in H0; simpl in H0.
      rewrite list_existsb_app, <- H0; simpl;  case (fp l[i]); simpl; auto.
    } {
      unfold existsb in *.
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      apply (f_equal negb) in H0; rewrite Bool.negb_involutive in H0; simpl in H0.
      rewrite list_existsb_app, <- H0; simpl;  case (fp l[i]); simpl; auto.
    }
  }
  { math.  }
  { rewrite take_zero; simpl; auto. }
  intros fin i_b Hind Hexists.
  xmatch.
  xapp.
  xvals*. {
    destruct fin; destruct Hind as [Hlen Himpl].
    - rewrite Bool.implb_true_l in Himpl.
      assert (Heq: i_b = length l) by (apply Z.eqb_eq; auto).
      rewrite Heq, take_full_length; auto.
    - simpl in Hexists.
      apply (f_equal negb) in Hexists; rewrite Bool.negb_involutive in Hexists; simpl in Hexists.
      rewrite <- Hexists.
      rewrite <- (@list_eq_take_app_drop _ i_b l) at 1.
      unfold existsb in *; rewrite list_existsb_app; rewrite <- Hexists; simpl; auto.
      math.
  }
Qed.
