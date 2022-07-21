Set Implicit Arguments.

Require Import Bool.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayExists Require Import Verify_array_exists_utils.
From ProofsArrayExists Require Import Array_exists_old_ml.

Lemma array_exists : forall A `{EA:Enc A} (l:list A) (arr: array A) (f: val),
   forall (I: list A -> hprop),
  (forall v t r, (l = t&v ++ r) ->
     SPEC (f v)
     PRE (I r)
     POST (fun acc: bool => if acc then I r  else I (v :: r))) ->
  SPEC (array_exists arr f)
    PRE (arr ~> Array l \* I nil)
    POST (fun b : bool => \exists l', if b then \[l' <> l] \* I l'  else \[l' = l] \* I l').
Proof using.
  intros. xcf; auto.
  xletopaque aux Haux.
  asserts Hrec : (forall (i : int) (r: list A),
                     r = (drop (i + 1) l) ->
                     -1 <= i < length l ->
                     SPEC (aux arr f i)
                          PRE (arr ~> Array l \* I r)
                          POST (fun b : bool => \exists l', if b then \[l' <> l] \* I l'  else \[l' = l] \* I l')).
  {
    intros i. induction_wf IH: (downto (-1)) i. intros r Hr Hi.
    xapp Haux.
    xif; => Hi_0.
    + xvals.
      asserts Hi_1 : (i = -1). { math. }
      rewrite Hr, Hi_1, drop_neg; (auto || math).
    + asserts Hlen: (length l > 0). { math. }
      pose proof (length_nonzero_cons l Hlen) as [_x [_l Hxl]].
      pose proof ((Inhab_of_val _x)).
      xapp.
      apply index_of_inbound; math.
      xapp.
      instantiate (1:= take i l).
      math_rewrite (i = i + 1 - 1).
      erewrite <- take_pos_last.
      { rewrite Hr. rewrite list_eq_take_app_drop; auto. math. }
      { apply int_index_prove; math. }
      intros [|]; xif; => C; try (contradiction || rewrite not_True_eq in C; contradiction).
      ++ xvals.
         rewrite Hr.
         rewrite <- (@list_eq_take_app_drop A (i + 1) l) at 2.
         rewrite <- (@app_nil_l A (drop (i + 1) l)) at 1.
         intros contra.
         Check  (app_cancel_r nil (take (i + 1) l) (drop (i + 1) l)).
         apply (app_cancel_r nil (take (i + 1) l) (drop (i + 1) l)) in contra.

         rewrite <- Hxl in contra.
         rewrite take_cons in contra; (math || auto). discriminate contra.
         math.
      ++ xapp; try math.
         +++ unfold downto; math.
         +++ math_rewrite (i - 1 + 1 = i). rewrite Hr. symmetry. apply drop_cons'; (auto || math).
         +++ intros b t'. xsimpl*.
  }
  xapp. xapp; math || auto. math_rewrite (length l - 1 + 1 = length l). rewrite drop_at_length; auto.
  intros; xsimpl*.
Qed.
