Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayRev Require Import Common_ml.

Lemma index_cons (A: Type) `{IA: Inhab A} (ls: list A):
  LibListZ.length ls > 0 -> ls = ls[0] :: drop 1 ls.
Proof.
  case ls.
  - rewrite LibListZ.length_nil; math.
  - intros hd tl; rewrite read_zero.
    math_rewrite (1 = 0 + 1).
    rewrite drop_cons, drop_zero; try math; auto.
Qed.


Lemma list_split (A: Type) (l t r: list A) (v: A):
  l = t ++ v :: r ->
  LibList.rev l = LibList.rev r & v ++ LibList.rev t.
Proof.
  intros ->; rewrite rev_app; rew_list; auto.
Qed.

Lemma list_drop_sub (A: Type) (l: list A) (i : int):
  0 < i < length l ->
  list_sub (drop i l) l.
Proof.
  gen i; induction l.
  - intros i; rewrite drop_nil, length_nil; math.
  - rewrite length_cons; intros i Hi.
    rewrite drop_cons_pos; try math.
    case (Z.ltb_spec0 0 (i - 1)); intros Hzro.
    + apply list_sub_tail; apply IHl; math.
    + math_rewrite (i - 1 = 0); rewrite drop_zero; apply list_sub_cons.
Qed.      

Lemma div_2_ignore (i: int):
  (2 * i + 1) / 2 = i.
Proof.
  math_rewrite ((2 * i + 1) = 1 + i * 2).
  rewrite Z_div_plus; try math.
  rewrite <- Z.div2_div; simpl.
  rewrite Z.add_0_l.
  auto.
Qed.

Lemma list_half_ge (A: Type) (l: list A) :
  (length l / 2) <= length l.
Proof.
  cut (length l / 2 <= length l)%Z; try math.
  apply Z.div_le_upper_bound; try math.
Qed.

Lemma list_half_diag_leq (A: Type) (l: list A) :
  (length l / 2) + (length l / 2) <= length l.
Proof.
  case_eq (Z.odd (length l)); intros Hparity.
  + apply Zodd_bool_iff in Hparity; apply Zodd_ex in Hparity; destruct Hparity as [l_half_len Hhalf].
    rewrite Hhalf in *.
    rewrite !div_2_ignore, Z.add_diag; math.
  + rewrite Zodd_even_bool in Hparity; apply Bool.negb_false_iff in Hparity;
      apply Zeven_bool_iff in Hparity; apply Zeven_ex in Hparity; destruct Hparity as [l_half_len Hhalf].
    rewrite Hhalf in *.
    math_rewrite (2 * l_half_len = 0 + l_half_len * 2).
    rewrite !Z_div_plus; try math.
    rewrite <- Z.div2_div; simpl.
    rewrite -> Z.add_diag; math.
Qed.

Lemma list_half_le (A: Type) (l: list A):
    length l - (length l / 2) - 1 <= (length l / 2).
Proof.
  case_eq (Z.odd (length l)); intros Hparity.
  + apply Zodd_bool_iff in Hparity; apply Zodd_ex in Hparity; destruct Hparity as [l_half_len Hhalf].
    rewrite Hhalf.
    rewrite !div_2_ignore, <- Z.add_diag; try math.
  + rewrite Zodd_even_bool in Hparity; apply Bool.negb_false_iff in Hparity;
      apply Zeven_bool_iff in Hparity; apply Zeven_ex in Hparity; destruct Hparity as [l_half_len Hhalf].
    rewrite Hhalf in *.
    math_rewrite (2 * l_half_len = 0 + l_half_len * 2).
    rewrite !Z_div_plus; try math.
    rewrite <- Z.div2_div; simpl.
    math_rewrite (l_half_len * 2 = 2 * l_half_len).
    rewrite <- Z.add_diag; math.
Qed.

Lemma list_half_gt (A: Type) (l: list A) :
  length l > 0 ->
  (length l / 2) < length l.
Proof.
  intros Hlen.
  cut (length l / 2 < length l)%Z; try math.
  apply Z.div_lt_upper_bound; try math.
Qed.

Lemma list_half_prop (A: Type) (l: list A) :
  0 < (length l / 2) -> 0 < length l.
Proof.
  destruct l; rewrite ?length_nil, ?length_cons; try math.
  rewrite <- Z.div2_div; simpl; auto.
Qed.

Lemma list_half_pos (A: Type) (l: list A) :
  length l > 1 ->
  0 < (length l / 2).
Proof.
  intros Hlen.
  cut (0 < length l / 2)%Z; try math.
  apply Z.div_str_pos; try math.
Qed.

Lemma read_rev (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  0 <= i < length l ->
  l[i] = (LibList.rev l)[length l - i - 1].
Proof.
  gen i; induction l as [| l ls IHls].
  + intros i; rewrite length_nil; math.
  + intros i; rewrite length_cons; intros Hi.
    case (Z.eqb_spec i 0); intros Hi_zero.
    * rewrite Hi_zero, rev_cons, read_zero, read_last_case, If_l; auto; rewrite length_rev; math.
    * rewrite read_cons_pos, rev_cons, read_last_case, If_r; try rewrite length_rev; try math.
      rewrite IHls; try math.
      f_equal; math.
Qed.      
    

Lemma list_odd_index (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  i = length l -> i > 0 ->
  l[i / 2] = (LibList.rev l)[i / 2  + if Z.odd i then 0 else (- 1)].
Proof.
  intros -> Hgt.
  rewrite <- (@list_eq_take_app_drop _ (length l / 2)) at 1 3; try apply list_half_ge.
  rew_list.
  case_eq (Z.odd (length l)); intros Hparity.
  + generalize (Hparity); intros Hparity'; apply Zodd_bool_iff in Hparity'; apply Zodd_ex in Hparity'.
    destruct Hparity' as [l_half_len Hhalf].
    assert (Hlen: length l / 2 = l_half_len) by (rewrite Hhalf, div_2_ignore; auto).
    rewrite Hlen in *.
    rewrite read_app, length_take_nonneg, If_r; try math.
    rewrite read_app, length_rev, length_drop_nonneg, If_l; try math.
    math_rewrite (l_half_len - l_half_len = 0).
    math_rewrite (l_half_len + 0 = l_half_len).
    rewrite read_rev; try (rewrite length_drop_nonneg; math).
    rewrite length_drop_nonneg; try math.
    apply f_equal; math.
  + rewrite Zodd_even_bool in Hparity; apply Bool.negb_false_iff in Hparity;
      apply Zeven_bool_iff in Hparity; apply Zeven_ex in Hparity.
    destruct Hparity as [l_half_len Hhalf].
    assert (Hlen: length l / 2 = l_half_len)
      by (rewrite Hhalf, <- (Z.add_0_l (_ * _)), Z.mul_comm, Z_div_plus, Zdiv_0_l; try math).
    rewrite Hlen in *.
    rewrite !read_app.
    rewrite length_take_nonneg, length_rev, length_drop_nonneg; try math.
    rewrite If_r; try math.
    rewrite If_l; try math.
    math_rewrite (l_half_len - l_half_len = 0).
    math_rewrite (l_half_len + -1 = l_half_len - 1).
    clear Hlen.
    rewrite read_rev; try (rewrite length_drop_nonneg; math).
    rewrite length_drop_nonneg; try math.
    apply f_equal; math.
Qed.
