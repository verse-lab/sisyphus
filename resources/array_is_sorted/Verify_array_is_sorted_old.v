Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayIsSorted Require Import Verify_array_is_sorted_utils.
From ProofsArrayIsSorted Require Import Array_is_sorted_old_ml.

Fixpoint is_sorted_internal A (f_p: A -> A -> int) (x: A) (l: list A) :=
  match l with
  | nil => true
  | h :: t => (f_p x h <=? 0) && is_sorted_internal f_p h t
  end.

Definition is_sorted A (f_p: A -> A -> int) (l: list A) :=
  match l with
  | nil => true
  | h :: t => is_sorted_internal f_p h t
  end.

Lemma drop_read A `{EA: Enc A} (IA: Inhab A) (l: list A) (i: int) :
  0 < i <= length l  ->
  l[i - 1] :: drop i l = drop (i - 1) l.
Proof.
  intros.
  eapply eq_of_extens.
  + rewrite length_cons, !length_drop_nonneg; math.
  + intros j; rewrite index_eq_index_length, int_index_eq, length_cons, length_drop_nonneg;
      try math; intros H'.
    rewrite read_drop; [ | math | apply int_index_prove; try math ].
    case (Z.eqb_spec j 0); [intros -> | intros Heq];
      rewrite ?read_zero, ?read_cons_pos, 1?read_drop.
    all: (try apply int_index_prove); try f_equal; math.
Qed.

Lemma is_sorted_cons A (hd: A) (tl: list A) fp :
  is_sorted fp (hd :: tl) -> is_sorted fp tl.
Proof.
  case tl as [| hd2 tl]; simpl; auto; rewrite istrue_and_eq.
  intros []; auto.
Qed.

Lemma not_is_sorted_god_mode A `{EA: Enc A} (IA: Inhab A) (f_p: A -> A -> int) (l: list A) (i: int) :
  length l > 1 ->
  0 < i <= length l - 1 ->
  ~ f_p l[i-1] l[i] <= 0 ->
  ~ is_sorted f_p l.
Proof.
  intros H1 H2 Hf H_sorted; apply Hf; clear Hf; gen i H_sorted H2 H1.
  destruct l as [| hd tl]; [rewrite length_nil; math | ]; simpl.
  gen hd.
  induction tl as [| nxt_hd tl H].
  + intros hd i; rewrite length_cons, length_nil; math.
  + intros hd i; simpl; rewrite !length_cons, istrue_and_eq.
    intros [Hfp Hsorted_tl].
    math_rewrite (1 + (1 + length tl) - 1 = length tl + 1).
    intros Hi Hlen.
    case (Z.eqb_spec i 1); [intros -> | intros Hneq1].
    * math_rewrite (1 - 1 = 0).
      rewrite read_zero, read_cons_pos; try math.
      math_rewrite (1 - 1 = 0).
      rewrite read_zero.
      apply Z.leb_le; auto.
    * assert (i > 1) by math.
      rewrite read_cons_pos; try math.
      rewrite (read_cons_pos IA hd); try math.
      apply H; auto; try (rewrite length_cons; math).
Qed.




Lemma array_is_sorted : forall A `{EA:Enc A} (l:list A) (arr: array A) (f: val) (f_p: A -> A -> int),
    ( forall (x y: A),
        SPEC_PURE (f x y) POST (\[= f_p x y])
    ) ->
  SPEC (array_is_sorted arr f)
    PRE (arr ~> Array l)
    POST (fun b => \[b = is_sorted f_p l]).
Proof using.
  intros. xcf; auto.
  xletopaque rec Hrec.
  xapp.
  asserts Hrec_inv : (forall (i: credits) (t r: list A) ,
                         -1 <= i <= length l - 1  ->
                         r = drop i l ->
                         l = t ++ r ->
                         SPEC (rec arr f i)
                              PRE (arr ~> Array l \* \[is_sorted f_p r = true])
                              POST (fun b => \[b = is_sorted f_p l])
                     ).
  {
     intros i. induction_wf IH: (downto (-1)) i; intros t r Hi_bound Hrdrop Htr.
     apply (Hrec A EA arr f i).
     xpullpure Hr.
     xif ;=> C.
     + xvals.
       asserts Hi' : (-1 <= i <= 0). { math. }
       asserts Hi : (i = -1 \/ i = 0). {
         case (Z.leb_spec0 0 i).
         + intros. right. math.
         + intros. left. math.
       }

       destruct Hi as [Hi | Hi]; (rewrite Hi, ? drop_neg, ? drop_zero in Hrdrop; try math; rewrite <- Hrdrop, Hr; auto).
     + asserts Hlen : (0 < length l). { math. }
       destruct (length_nonzero_cons l Hlen) as [_x [_tl Hl]].
       pose (Inhab_of_val _x) as IA.
       xapp. { apply int_index_prove; math.  }
       xapp. { apply int_index_prove; math. }
       xapp (H l[i-1] l[i]).
       xif ;=> C2.
       ++ xapp.
          +++ unfold downto. math.
          +++ math.
          +++ instantiate (1:= l[i-1] :: r). rewrite Hrdrop.
              rewrite drop_read; (try math || auto).
          +++ instantiate (1:= take (i - 1) l). rewrite Hrdrop, drop_read, list_eq_take_app_drop; (try math || auto).
          +++ asserts Hr_cons : (exists h tl, r = h :: tl /\  h = l[i]). {
                exists l[i], (drop (i + 1) l).
                split; auto.
                math_rewrite (i = i + 1 - 1).
                math_rewrite (i + 1 - 1 + 1 = i + 1).
                assert (i >= 1) by math.
                rewrite (@drop_read A EA IA l (i + 1)); auto.
                math_rewrite (i + 1 - 1 = i).
                exact Hrdrop.
                math.
              }
              destruct Hr_cons as [h [tl [H_r_eq H_r_read]]].
              simpl.
              rewrite H_r_eq; simpl.
              rewrite H_r_eq in Hr; simpl in Hr.
              rewrite Hr.
              rewrite istrue_and_eq. split; auto.
              rewrite istrue_eq_eq_true.
              apply Zle_is_le_bool.
              rewrite <- le_zarith.
              rewrite H_r_read.
              auto.
          +++ xsimpl*.
       ++ xvals. apply (@not_is_sorted_god_mode _ _ _ _ _ i); (try math || auto).
  }

  case l as [| h l'] eqn: Heq.

  {
  xapp Hrec_inv.
  + rew_list. math.
  + instantiate (1:= nil). rew_list. math_rewrite (0 - 1 = -1). rewrite drop_neg; try math || reflexivity.
  + instantiate (1:= nil). rew_list. reflexivity.
  + auto.
  + xsimpl*; auto.
  }

  {
    pose (Inhab_of_val h) as IA.
    pose  (l[length l - 1] :: nil).
    xapp Hrec_inv.
    + rew_list. math.
    + instantiate (1:= l0).
      rewrite <- Heq.
      rewrite <- (@drop_read A EA IA l (length l)).
      ++ rewrite drop_at_length. auto.
      ++ rewrite Heq; rew_list; math.
    + rewrite <- Heq. unfold l0.
      instantiate (1:= take (length l - 1) l).
      rewrite <- take_full_length at 1.
      apply take_pos_last.
      apply int_index_prove; auto.
      ++  rewrite Heq. rew_list. math.
      ++ math.
    + simpl; auto.
    + xsimpl*.
  }
Qed.
