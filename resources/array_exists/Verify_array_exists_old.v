Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
From ProofsArrayExists Require Import Verify_array_exists_utils.
From ProofsArrayExists Require Import array_exists_old_ml.


Lemma to_array_spec :
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
  xapp;=> result.
  xletopaque tmp Htmp.
  xapp (@while_upto_spec 0 (length l) tmp
           (fun i b => \[negb b = List.existsb fp (take i l)] \*
                         result ~~> (List.existsb fp (take i l)) \*
                         a ~> Array l)
       ). {
    intros i Hi.
    apply Htmp.
    assert (IA: Inhab A). {
      destruct l; rew_list in Hi; try math.
      apply Inhab_of_val; auto.
    }
    xpullpure Hexists.
    xapp. { apply int_index_prove; math. }
    xapp (H l[i]).
    xapp.
    xapp.
    xvals. {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite list_existsb_app, <- Hexists; simpl;  case (fp l[i]); simpl; auto.
    }
    {
      rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
      math_rewrite ((i + 1 - 1) = i).
      rewrite list_existsb_app, <- Hexists; simpl;  case (fp l[i]); simpl; auto.
    }
  }
  { math.  }
  { rewrite take_zero; simpl; auto. }
  intros [|] i_b [Hlen Himpl] Hexists; xmatch; xapp; xsimpl*.
  - rewrite Bool.implb_true_l in Himpl.
    assert (Heq: i_b = length l) by (apply Z.eqb_eq; auto).
    rewrite Heq, take_full_length; auto.
  - simpl in Hexists.
    rewrite <- Hexists.
    rewrite <- (@list_eq_take_app_drop _ i_b l) at 1.
    rewrite list_existsb_app; rewrite <- Hexists; simpl; auto.
    math.
Qed.
