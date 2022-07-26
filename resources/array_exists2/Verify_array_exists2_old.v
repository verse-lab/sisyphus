Set Implicit Arguments.

Require Import Bool.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayExists2 Require Import Verify_array_exists2_utils.
From ProofsArrayExists2 Require Import Array_exists2_old_ml.


Lemma array_exists2_noneq : forall A B `{EA:Enc A}  `{EB:Enc B} (l1:list A) (arr1: array A) (l2:list B) (arr2: array B) (f: val),
    length l1 <> length l2 ->
    SPEC (array_exists2 arr1 arr2 f)
    PRE (arr1 ~> Array l1 \* arr2 ~> Array l2 )
    POST (fun b : bool => \[b = false]).
Proof using.
  intros. xcf; auto.
  xletopaque aux Haux.
  xapp. xapp. xletopaque b Hb.
  xif; => C.
  + rewrite C in Hb. symmetry in Hb.
    apply (istrue_isTrue_forw (length l1 = length l2)) in Hb.
    contradiction.
  + xvals. intros [].
Qed.


Lemma array_exists2_eq : forall A B `{EA:Enc A} `{EB: Enc B} (l1:list A) (arr1: array A) (l2:list B) (arr2: array B) (f: val),
    length l1 = length l2 ->
  forall (I: list A -> list B -> hprop),
  (forall v1 t1 r1 v2 t2 r2, (l1 = t1&v1 ++ r1) -> (l2 = t2&v2 ++ r2) ->
     SPEC (f v1 v2)
     PRE (I r1 r2)
     POST (fun acc: bool => if acc then I r1 r2  else I (v1 :: r1) (v2 :: r2))) ->
  SPEC (array_exists2 arr1 arr2 f)
    PRE (arr1 ~> Array l1 \* arr2 ~> Array l2 \* I nil nil)
    POST (fun b : bool => \exists l1' l2',  if b then \[l1' <> l1 /\ l2' <> l2] \* I l1' l2' else \[l1' = l1 /\ l2' = l2] \* I l1' l2').
Proof using.
  intros. xcf; auto.
  xletopaque aux Haux.
    asserts Hrec : (forall (i : int) (r1: list A) (r2: list B),
                     r1 = (drop (i + 1) l1) ->  r2 = (drop (i + 1) l2) ->
                     -1 <= i < length l1 ->
                     SPEC (aux arr1 arr2 f i)
                          PRE (arr1 ~> Array l1 \* arr2 ~> Array l2 \* I r1 r2)
                          POST (fun b : bool => \exists l1' l2',  if b then \[l1' <> l1 /\ l2' <> l2] \* I l1' l2' else \[l1' = l1 /\ l2' = l2] \* I l1' l2')).
    {
      intros i. induction_wf IH: (downto (-1)) i. intros r1 r2 Hr1 Hr2 Hi.
      asserts Hi2: (-1 <= i < length l2). by math.
      xapp Haux.
      xif; => Hi0.
      + xvals.
        asserts Hi_1 : (i = -1). { math. }
        rewrite Hr1, Hr2, Hi_1, drop_neg; auto. math.
      + asserts Hlen1: (length l1 > 0). { math. }
        asserts Hlen2: (length l2 > 0). { math. }
        pose proof (length_nonzero_cons l1 Hlen1) as [_x [_l Hxl]].
        pose proof ((Inhab_of_val _x)).
        pose proof (length_nonzero_cons l2 Hlen2) as [_x2 [_l2 Hxl2]].
        pose proof ((Inhab_of_val _x2)).
        xapp; auto. xapp; auto. xapp; auto.
        instantiate (1:= take i l1). rewrite Hr1. apply take_read_app; (auto || math).
        instantiate (1:= take i l2). rewrite Hr2. apply take_read_app; (auto || math).
        intros [|]; xif; => C;  try (contradiction || rewrite not_True_eq in C; contradiction).
        ++ xvals. split.
           +++ rewrite Hr1.
               apply (@neq_drop_list A EA H1 i l1 _x _l); try math; auto.
            +++ rewrite Hr2.
               apply (@neq_drop_list B EB H2 i l2 _x2 _l2); try math; auto.
        ++ xapp; try unfold downto; try math; ((try rewrite Hr1; try rewrite Hr2; try math_rewrite (i - 1 + 1 = i); symmetry; apply drop_cons'; (auto || math)) || intros; xsimpl*).
    }
    xapp. xapp. xletopaque b Hb.
    xif ;=> C. xapp. xapp; auto.
  + math_rewrite (length l1 -1 +1 = length l1). rewrite drop_at_length; auto.
  + math_rewrite (length l1 -1 + 1 = length l2). rewrite drop_at_length; auto.
  + math.
  + intros. xsimpl*.
  + rewrite isTrue_eq_true in Hb. contradiction. exact H.
Qed.
