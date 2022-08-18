Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayMap2 Require Import Common_ml.



Fixpoint map2 (A B C: Type) (f: A -> B -> C) xs ys :=
  match xs, ys with
  | nil, nil => nil
  | x :: xs, y :: ys => f x y :: map2 f xs ys
  | _, _ => nil
  end.

Lemma length_map2_l (A B C: Type) (f: A -> B -> C) xs ys :
  LibListZ.length xs = LibListZ.length ys ->
  LibListZ.length (map2 f xs ys) = LibListZ.length xs.
Proof.
  gen ys. induction xs as [ |  x xs IHxs].
  -  intros ys. rewrite length_nil; => Hxs; symmetry in Hxs.
     apply length_zero_inv in Hxs; rewrite Hxs; simpl.
     rewrite length_nil; auto.
  - intros [| y ys]; try (rewrite length_cons, length_nil; math).
    simpl; rewrite !length_cons; intros Hlen.
    rewrite IHxs; math.
Qed.    

Lemma map2_index
  (A B C: Type) `{IA: Inhab A} `{IB: Inhab B} `{IC: Inhab C} i (f: A -> B -> C) xs ys:
  LibListZ.length xs = LibListZ.length ys -> 0 <= i < LibListZ.length xs ->
  (map2 f xs ys)[i] = f xs[i] ys[i].
Proof.
  gen i ys; induction xs as [ | x xs IHxs].
  + intros i ys; rewrite length_nil; => Hxs; symmetry in Hxs; math.
  + intros i [| y ys]; try (rewrite length_cons, length_nil; math).
    simpl; rewrite !length_cons; intros Hlen Hi.
    case_eq (Z.eqb_spec i 0).
    * intros Hi0 _. rewrite Hi0, !read_zero; auto.
    * intros Hn0 _. rewrite !read_cons_pos; try math.
      rewrite IHxs; try math; auto.
Qed.

Lemma drop_make (A: Type) (i len: int) (vl: A):
  0 <= i <= len -> drop i (make len vl) = make (len - i) vl.
Proof.
  gen len vl.
  induction_wf IH: (downto 0) i.
  intros len vl Hi.
  case_eq (Z.eqb_spec i 0).
  + intros Hi0 _. rewrite Hi0; rewrite drop_zero; f_equal; math.
  + intros Hn0 _; assert (Higt: i > 0) by math.
    rewrite make_eq_cons_make_pred; try math.
    rewrite drop_cons_pos; try math.
    rewrite IH; try math; try (apply downto_intro; math).
    f_equal; math.
Qed.  
