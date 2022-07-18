Set Implicit Arguments.

From CFML Require Import WPLib Stdlib WPTactics WPLifted WPHeader WPBuiltin.
From TLC Require Import LibListZ.

From ProofsArrayOfRevList Require Import Verify_array_of_rev_list_utils.
From ProofsArrayOfRevList Require Import Array_of_rev_list_new_ml.


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
    xletopaque f Hf.
    Check (@iteri_spec _ _ l f (fun t => arr ~> Array (drop (length t) data ++ rev t))).
    xapp (@iteri_spec _ _ (x :: l') f
            (fun t => arr ~> Array (drop (length t) data ++ rev t))
         ).
    {
      =>> Hx Hi.
      apply Hf. xapp.
      assert (i < len) as Hilen. { rewrite Hlen. rewrite Hx. rewrite length_app. rewrite Hi. rewrite length_cons. math. }
      + rewrite index_eq_index_length, length_app, length_rev.
        rewrite <- Hi.
        rewrite length_drop_nonneg; try math.

        apply int_index_prove; ((rewrite Hdata, length_make; math) || math).
        rewrite Hdata, length_make; math.
      + xsimpl*.
    } {
      rew_list. rewrite drop_zero. auto.
    }
    xvals. {
      rewrite <- H.
      assert (length l = length data) as Hl_data. { rewrite H, Hdata, length_make. rewrite <- Hlen; auto. math. }
      rewrite Hl_data, drop_at_length. rew_list. reflexivity.
    }
Admitted.
