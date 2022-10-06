Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

Fixpoint findi (A: Type) (i: int) (f: int -> A -> bool) (ls: list A) : option (int * A) :=
  match ls with
  | nil => None
  | h :: t =>
      if f i h then Some (i, h)
      else findi (i + 1) f t
  end.

Lemma findi_app_r (A: Type) (B: Type) i (f: int -> A -> bool) l1 l2:
  findi i f l1 = None ->
  (findi i f (l1 ++ l2)) = findi (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_app_l (A: Type) i (f: int -> A -> bool) l1 l2:
  is_some (findi i f l1) ->
  (findi i f (l1 ++ l2)) = findi i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.



Fixpoint findi_map (A: Type) (B: Type) (i: int) (f: A -> option B) (ls: list A) : option (int * B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (i, v)
      | None => findi_map (i + 1) f t
      end
  end.

Lemma findi_map_app_r (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  findi_map i f l1 = None ->
  (findi_map i f (l1 ++ l2)) = findi_map (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_map_app_l (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  is_some (findi_map i f l1) ->
  (findi_map i f (l1 ++ l2)) = findi_map i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.

Fixpoint find_map (A: Type) (B: Type) (f: A -> option B) (ls: list A) : option (B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (v)
      | None => find_map f t
      end
  end.

Lemma find_map_app_r (A: Type) (B: Type) (f: A -> option B) l1 l2:
  find_map f l1 = None ->
  (find_map f (l1 ++ l2)) = find_map f l2.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
Qed.

Lemma find_map_app_l (A: Type) (B: Type) (f: A -> option B) l1 l2:
  is_some (find_map f l1) ->
  (find_map f (l1 ++ l2)) = find_map f l1.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros l2; rew_list; simpl.
    case_eq (f a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.

Lemma list_existsb_app (A: Type) (l1 l2: list A) (fp: A -> bool):
  List.existsb fp (l1 ++ l2) =
    List.existsb fp l1 || List.existsb fp l2.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; rewrite if_then_true_else_false; auto.
  - intros l2; rewrite app_cons_l; simpl; rewrite IHl1; simpl.
    case (fp a); simpl; auto.
Qed.


Lemma list_fold_length_rev : forall A (xs : list A),
    List.fold_left
         (fun '((i,acc) : credits * list A) (x : A) => (i + 1, x :: acc)) xs (0, nil) =
      (length xs, rev xs).
Proof.
  intros A.
  cuts G: (forall (xs : list A)  (i: int) (init: list A),
          List.fold_left
            (fun '((i,acc) : credits * list A) (x : A) =>
               (i + 1, x :: acc))
            xs (i, init) = (i + length xs, rev xs ++ init)). {
    intros xs; rewrite G. f_equal; rew_list; auto.
  }
  intros xs; induction xs as [| x xs IHxs]; simpl.
  - intros i init; rew_list; f_equal; auto; math.
  - intros i init; simpl.
    rewrite IHxs.
    rewrite !length_cons.
    f_equal; try math. rew_list; auto.
Qed.

Lemma drop_last: forall A (xs rst: list A) (lst: A),
    rev xs = lst :: rst ->
    drop (length xs - 1) xs = lst :: nil.
Proof.
  intros A xs. induction_wf IH: list_sub xs.
  case_eq xs.
  - intros Hxs rst lst; rewrite rev_nil; intros H; inversion H.
  - intros hd tl Hxs; intros rst lst Hlst; rewrite length_cons.
    math_rewrite ((1 + length tl - 1) = length tl).
    case_eq tl.
    * intros Htl. rewrite Htl in *. rewrite rev_cons in Hlst.
      rewrite last_nil in Hlst.
      rewrite length_nil; rewrite drop_zero.
      f_equal. inversion Hlst; auto.
    * intros y ys Hys; rewrite length_cons.
      math_rewrite (1 + length ys = length ys + 1).
      rewrite drop_cons; try math.
      asserts Hlen: ((length ys) = length (y :: ys) - 1). {
        rewrite length_cons; math.
      } rewrite Hlen; clear Hlen.
      rewrite <- Hys.
      rewrite rev_cons in Hlst.
      rewrite <- (app_cons_one_r lst) in Hlst.
      assert (lst :: nil = nil & lst) by  (rew_list; auto).
      rewrite H in Hlst.
      assert (Hlst' := Hlst).
      apply last_eq_middle_inv in Hlst.
      case Hlst; clear Hlst.
      ** intros [Htl [Hlsthd Hrd] ].
         (* B109 *)
         apply rev_eq_nil_inv in Htl.
         rewrite Htl in Hys; inversion Hys.
      ** intros [rst_but_last Hrst].
         eapply (IH tl _ rst_but_last lst).
         rewrite Hrst in Hlst'.
         rewrite <- last_app in Hlst'.
         apply last_eq_last_inv in Hlst'.
         case Hlst' as [H1 H2].
         rewrite H1.
         rewrite app_last_l.
         rewrite app_nil_l.
         auto.
         Unshelve.
         rewrite Hxs. apply list_sub_cons.
Qed.

Lemma drop_nth : forall A l v r i (xs: list A),
    xs = l ++ v :: r ->
    i = length l ->
    drop i xs = v :: drop (i + 1) xs.
Proof.
  intros A l v r i xs -> ->.
  rewrite drop_app_length.
  rewrite app_cons_r.
  assert ((length l + 1) = length (l & v)) as H by (rewrite length_last; math).
  rewrite H.
  rewrite drop_app_length.
  auto.
Qed.

Lemma case_rev_split : forall A (xs: list A) v l r,
    rev xs = l ++ v :: r ->
    xs = rev r ++ v :: rev l.
Proof.
  intros A xs; induction xs.
  - intros v l r; rewrite rev_nil; intros Hnil.
    apply nil_eq_app_inv in Hnil. case Hnil as [H1 H2].
    inversion H2.
  - intros v l r.
    intros Hr; assert (Hr' := Hr).
    rewrite rev_cons in Hr. rewrite (app_cons_r v) in Hr.
    apply last_eq_middle_inv in Hr.
    case Hr.
    * intros [Hrevls [Ha Hnil]].
      rewrite Hnil. rewrite rev_nil.
      rewrite app_nil_l. rewrite Ha.
      apply f_equal.
      rewrite <- Hrevls.
      rewrite rev_rev.
      auto.
    * intros [pre Hrpre].
      rewrite Hrpre in Hr'.
      rewrite rev_cons in Hr'.
      rewrite <- last_cons in Hr'.
      rewrite <- last_app in Hr'.
      apply last_eq_last_inv in Hr'.
      case Hr' as [H1 H2].
      rewrite (IHxs _ _ _ H1).
      rewrite Hrpre.
      rewrite rev_last.
      rew_list.
      auto.
Qed.

Lemma read_rev_helper (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  0 <= i < length l ->
  l[i] = (rev l)[length l - i - 1].
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

Lemma read_rev (A: Type) `{IA: Inhab A} (l: list A) (i: int):
  0 <= i < length l ->
  (rev l)[i] = l[length l - i - 1].
Proof.
  intros Hvld.
  rewrite (read_rev_helper l); try math.
  f_equal.
  math.
Qed.

Lemma make_rev_update: forall (A: Type) (x v: A) (t r: list A),
    (make (length r + 1) x ++ take (length t) (rev t))[length r:=v] =
  make (length r) x ++ take (1 + length t) (v :: rev t).
Proof.
  intros.
  rewrite make_succ_r; [|math].
  rewrite app_last_l, update_middle; rewrite ?length_make; try math.
  rewrite take_cons_pos; try math.
  rewrite app_last_l; repeat f_equal; try math.
Qed.
