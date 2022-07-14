Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_old_ml.


Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof.
  xcf.
  case l as [ | x l'] eqn: H.
  - xmatch_case_0.
    xapp. xsimpl.
  - xmatch.
    xletopaque len Hlen.
    xalloc arr data Hdata.
    xapp. intros r.
    xletopaque loop Hloop.
    asserts Hrec : (forall i : int, -1 <= i <= len - 2 ->
                                SPEC (loop i)
                                     PRE (r ~> Ref (drop (len - (i + 1)) l)
                                            \*
                                            arr ~> Array (take (i + 1) data ++ rev (take (len - (i + 1)) l)) )
                                     POSTUNIT (r ~>  Ref (drop len l)
                                                 \*
                                                 arr ~> Array (rev l))).
    {
      intros i. induction_wf IH: (downto (-1)) i; intros.
      apply Hloop.
      xif; => Hi.
      {
      xapp.
      assert (Hlen_new : 0 <= len - (i + 1) < length l). {  rewrite Hlen, H.  math. }
      pose proof (@drop_cons_two _ l (len - (i + 1)) Hlen_new).
      destruct H1 as [hd [r' Heq]].
      erewrite drop_nth.
      + xlet.
        Check hd_spec.
        xapp hd_spec.
        instantiate (1 := hd).
        instantiate (1 :=  drop (len - (i + 1) + 1) l).
        auto. xpull. intros. xapp. auto.
        rewrite index_eq_index_length.
        apply int_index_prove; try math.
        rewrite length_app, length_take; try math.
        rewrite Hdata, length_make; subst; math.

        xapp.
        xapp tl_spec.
        auto.
        xapp.
        xapp; (unfold downto; try math || math).
        ++ math_rewrite (len - (i + 1) + 1 = len - i).
           math_rewrite (len - (i - 1 + 1) = len - i).
           reflexivity.
        ++ rewrite update_app_l.
           About update_app_l.
           +++  math_rewrite (len - (i + 1) = len - i - 1).
                About take_pos_last.
               rewrite (@take_pos_last _ (Inhab_of_val hd)).
               math_rewrite (i - 1 + 1 = i).
               math_rewrite (i + 1 - 1 = i).
               erewrite update_app_r. instantiate (1 := 0).
               rewrite update_zero, H1. rew_list. f_equal.
               rewrite (@take_pos_last _ (Inhab_of_val hd) _ (len - i)).
               rewrite rev_app.
               rew_list.
               f_equal.
               Locate "m [ b ]".
               pose proof @list_eq_take_app_drop A (len - (i + 1)) l .
               erewrite <- H2.
               erewrite read_app.
               rewrite length_take.
               assert (Z.max 0 (len - (i + 1)) = len - (i + 1)) as Hz. {  math. }
               rewrite Hz.
               assert (~ len - i - 1 < len - (i + 1)). {
                 math.
               }
               case_if.
               math_rewrite (len - i - 1 - (len - (i + 1)) = 0).
               rewrite Heq, read_zero. auto.
               rewrite H. rewrite <- Hlen. math. math.
               rewrite index_eq_index_length.
               apply int_index_prove; try math.
               instantiate (1 := i).
               rewrite length_take; auto. math.
               rewrite Hdata, length_make; (subst; math; auto).
               math. math.
               rewrite index_eq_index_length.
               apply int_index_prove; try math.
               rewrite Hdata, length_make. math. math.

           +++ rewrite length_take. math. rewrite Hdata.
               rewrite length_make. math. math.
        ++ xsimpl*.
      + instantiate (1 := r').
        instantiate (1 := take (len - (i + 1)) l).
        rewrite <- Heq.
        rewrite list_eq_take_app_drop; (auto || subst; math).
      + rewrite length_take_nonneg; math.
      }

      xval.
      assert (Hi_minus_1 : i = -1). { math. }.
      rewrite Hi_minus_1.
      xsimpl*.
      math_rewrite ((len - (-1 + 1)) = len).
      reflexivity.
      math_rewrite ( (-1 +1) = 0).
      math_rewrite ((len - 0) = len).
      rewrite take_zero. rew_list.
      rewrite Hlen. rewrite <- H. rewrite take_full_length. reflexivity.
    }

    (* now, we reason about the loop *)
    xapp Hrec.
    {
      split; try math.
      rewrite Hlen. rew_list. math.
    }
    {
       math_rewrite (len - (len - 2 + 1) = 1).
    rewrite H.
    rewrite drop_cons_pos; try math. math_rewrite (1 - 1 = 0). rewrite drop_zero.
    reflexivity.
    }

    {
          math_rewrite ((len - (len - 2 + 1)) = 1).
    rewrite H, take_cons_pos; try math.
    math_rewrite ( 1 - 1 = 0).
    rewrite take_zero.
    rew_list.
    math_rewrite (len - 2 + 1 = len - 1).
    rewrite Hdata.
    math_rewrite (len = len - 1 + 1).
    rewrite make_succ_r at 2.
    rewrite take_app_l; try math.
     math_rewrite (len -1 + 1 = len).
    assert (Hlen_new : len - 1 = length (make (len - 1) x)). {
      rewrite length_make; (auto || subst; rew_list; math).
    }
    rewrite Hlen_new at 1.
    rewrite take_full_length.
    rewrite <- make_succ_r.
    math_rewrite (len - 1 + 1 = len).
    reflexivity.
    math. rewrite length_make; try math. rewrite Hlen. rew_list. math.  rewrite Hlen. rew_list. math.
    }

    xvals. { rewrite H. reflexivity. }
Qed.
