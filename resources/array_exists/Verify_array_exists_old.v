Set Implicit Arguments.

Require Import Bool.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Require Import Logic.FunctionalExtensionality.

From ProofsArrayExists Require Import Verify_array_exists_utils.
From ProofsArrayExists Require Import Array_exists_old_ml.

(* add boolean to invariant *)
Lemma array_exists_spec : forall {A} `{EA:Enc A} (l:list A) (arr: array A) (f: val),
   forall (I: list A -> bool -> hprop),
  (forall v t r, (l = t&v ++ r) ->
     SPEC (f v)
     PRE (I r false)
     POST (fun acc: bool => I (v :: r) acc)) ->
  SPEC (array_exists arr f)
    PRE (arr ~> Array l \* I nil false)
    POST (fun b : bool => if b then \exists t v r,  \[(l = t&v ++ r)
                               ] \* I (v :: r) true else  I l false).
Proof using.
  intros. xcf; auto.
  xletopaque aux Haux.
  asserts Hrec : (forall (i : int) (r: list A),
                     r = (drop (i + 1) l) ->
                     -1 <= i < length l ->
                     SPEC (aux arr f i)
                          PRE (arr ~> Array l \* I r false)
                          POST (fun b : bool => if b then \exists t v r,  \[(l = t & v ++ r)
                               ] \* I (v :: r) true else  I l false)).
  {
    intros i. induction_wf IH: (downto (-1)) i. intros r Hr Hi.
    xapp Haux.
    xif; => Hi_0.
    + xvals.
      asserts Hi_1 : (i = -1). { math. }
      rewrite Hr, Hi_1, drop_neg; (auto || xsimpl* || math).
    + asserts Hlen: (length l > 0). { math. }
      pose proof (length_nonzero_cons l Hlen) as [_x [_l Hxl]].
      pose proof ((Inhab_of_val _x)).
      xapp.
      apply index_of_inbound; math.
      xapp H.
      instantiate (1:= take i l).
      math_rewrite (i = i + 1 - 1).
      erewrite <- take_pos_last.
      { rewrite Hr. rewrite list_eq_take_app_drop; auto. math. }
      { apply int_index_prove; math. }
      intros [|]; xif; => C; try (contradiction || rewrite not_True_eq in C; contradiction).
      ++ xvals.
         instantiate (1:= take i l).
         rewrite Hr, app_last_l. rewrite <- drop_cons'; auto. rewrite list_eq_take_app_drop; (auto || math). math.
      ++ xapp; try math.
         +++ unfold downto; math.
         +++ math_rewrite (i - 1 + 1 = i). rewrite Hr. symmetry. apply drop_cons'; (auto || math).
         +++ intros b. xsimpl*.
  }
  xapp. xapp; math || auto. math_rewrite (length l - 1 + 1 = length l). rewrite drop_at_length; auto.
  intros; xsimpl*.
Qed.

Fixpoint fix_exists {A: Type} (l: list A) (f_p: A -> bool) : bool:=
  match l with
  | nil => false
  | x :: l' => (f_p x || fix_exists l' f_p)%bool
  end.

Lemma fix_exists_part {A:Type} (f_p: A -> bool) (l1 : list A) (l2 : list A) :
  fix_exists (l1 ++ l2) f_p = ((fix_exists l1 f_p) ||  (fix_exists l2 f_p))%bool.
Proof.
  intros. gen l2. induction l1; intros.
  + assert (fix_exists nil f_p = false). { auto. }
    rew_list. rewrite H. simpl.  auto.
  + simpl. rewrite app_cons_l. simpl. rewrite IHl1.
    rewrite orb_assoc. auto.
    Print or.
Qed.

Lemma array_exists_pure_spec : forall A `{EA:Enc A} (l:list A) (arr: array A) (f: val) (f_p: A -> bool),
    (forall (x :A),
        SPEC_PURE (f x)
        POST (\[= f_p x])
    ) ->
  SPEC (array_exists arr f)
    PRE (arr ~> Array l)
    POST (fun b : bool => \[Bool.eqb b (fix_exists l f_p)]).
Proof using.
  intros.
  pose (fun (ls: list A) (b: bool) => \[if b then fix_exists l f_p = true else fix_exists ls f_p = false]) as I.
  assert (arr ~> Array l = arr ~> Array l \* I nil false). {
    unfold I.
    apply himpl_antisym. xsimpl*. xsimpl*.
  }
  rewrite H0.
  xapp (@array_exists_spec A EA l arr f (I)).
  {

    intros v t r Hl. xapp. unfold I.
    case_eq (f_p v).
    + intros. xsimpl*. rewrite Hl. intros.
      rewrite app_last_l.
      Check (fix_exists_part f_p t (v :: r)).
      rewrite fix_exists_part. simpl. rewrite H1, H2. simpl.
      rewrite orb_true_r. auto.
    + intros. xsimpl*. intros. simpl. rewrite H1, H2. auto.
  }
  intros b. case b as [|] eqn: Hb.
  + unfold I.
    xsimpl*. intros t v r Hl ->. auto.
  + unfold I. xsimpl*. intros ->; auto.
Qed.
