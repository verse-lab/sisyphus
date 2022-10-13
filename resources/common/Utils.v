Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

Lemma negb_eq_neg (b: bool):
  negb b = ! b.
Proof.
  case b; simpl; auto.
Qed.


Fixpoint list_findi_internal (A: Type) (i: int) (f: int -> A -> bool) (ls: list A) : option (int * A) :=
  match ls with
  | nil => None
  | h :: t =>
      if f i h then Some (i, h)
      else list_findi_internal (i + 1) f t
  end.

Definition list_findi (A: Type) (f: int -> A -> bool) (ls: list A) : option (int * A) :=
  list_findi_internal 0 f ls.

Lemma findi_unfold (A: Type) (f: int -> A -> bool) (ls: list A) :
  list_findi f ls = list_findi_internal 0 f ls.
Proof. auto. Qed.

Lemma findi_app_r (A: Type) (B: Type) i (f: int -> A -> bool) l1 l2:
  list_findi_internal i f l1 = None ->
  (list_findi_internal i f (l1 ++ l2)) = list_findi_internal (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_app_l (A: Type) i (f: int -> A -> bool) l1 l2:
  is_some (list_findi_internal i f l1) ->
  (list_findi_internal i f (l1 ++ l2)) = list_findi_internal i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.

Fixpoint list_findi_map_internal (A: Type) (B: Type) (i: int) (f: A -> option B) (ls: list A) : option (int * B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (i, v)
      | None => list_findi_map_internal (i + 1) f t
      end
  end.

Definition list_findi_map (A: Type) (B: Type) (f: A -> option B) (ls: list A) : option (int * B) :=
  list_findi_map_internal 0 f ls.

Lemma findi_map_unfold (A: Type) (B: Type) (f: A -> option B) (ls: list A) :
  list_findi_map f ls = list_findi_map_internal 0 f ls.
Proof. auto. Qed.

Lemma findi_map_app_r (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  list_findi_map_internal i f l1 = None ->
  (list_findi_map_internal i f (l1 ++ l2)) = list_findi_map_internal (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma findi_map_app_l (A: Type) (B: Type) i (f: A -> option B) l1 l2:
  is_some (list_findi_map_internal i f l1) ->
  (list_findi_map_internal i f (l1 ++ l2)) = list_findi_map_internal i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.

Fixpoint list_find_mapi_internal (A: Type) (B: Type) (i: int)
  (f: int -> A -> option B) (ls: list A) : option B :=
  match ls with
  | nil => None
  | h :: t =>
      match f i h with
      | Some v => Some v
      | None => list_find_mapi_internal (i + 1) f t
      end
  end.

Definition list_find_mapi (A: Type) (B: Type)
  (f: int -> A -> option B) (ls: list A) : option B :=
  list_find_mapi_internal 0 f ls.

Lemma find_mapi_unfold  (A: Type) (B: Type) (f: int -> A -> option B) (ls: list A) :
  list_find_mapi f ls = list_find_mapi_internal 0 f ls.
Proof. auto. Qed.

Lemma find_mapi_singleton (A: Type) (B: Type) (f: int -> A -> option B) (i: int) (x: A):
  list_find_mapi_internal i f (x :: nil) = f i x.
Proof.
  simpl.
  case (f i x); auto.
Qed.

Lemma find_mapi_app_r (A: Type) (B: Type) i (f: int -> A -> option B) l1 l2:
  list_find_mapi_internal i f l1 = None ->
  (list_find_mapi_internal i f (l1 ++ l2)) = list_find_mapi_internal (i + length l1) f l2.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
    f_equal; try math.
Qed.

Lemma find_mapi_app_l (A: Type) (B: Type) i (f: int -> A -> option B) l1 l2:
  is_some (list_find_mapi_internal i f l1) ->
  (list_find_mapi_internal i f (l1 ++ l2)) = list_find_mapi_internal i f l1.
Proof.
  gen i l2; induction l1.
  - intros i l2; simpl; rew_list; intros Hf. inversion Hf.
  - intros i l2; rew_list; simpl.
    case_eq (f i a); intros; simpl. try inversion H0; auto.
    rewrite IHl1; auto.
Qed.


Fixpoint list_find_map (A: Type) (B: Type) (f: A -> option B) (ls: list A) : option (B) :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some v => Some (v)
      | None => list_find_map f t
      end
  end.

Lemma find_map_app_r (A: Type) (B: Type) (f: A -> option B) l1 l2:
  list_find_map f l1 = None ->
  (list_find_map f (l1 ++ l2)) = list_find_map f l2.
Proof.
  gen l2; induction l1.
  - intros l2; simpl; rew_list; auto; intros _; repeat f_equal; math.
  - intros l2; rew_list; simpl.
    case_eq (f a); intros; simpl; try inversion H0.
    rewrite IHl1; auto.
Qed.

Lemma find_map_app_l (A: Type) (B: Type) (f: A -> option B) l1 l2:
  is_some (list_find_map f l1) ->
  (list_find_map f (l1 ++ l2)) = list_find_map f l1.
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

Fixpoint filter_not (A: Type) (fp: A -> Prop) (ls: list A) : list A :=
  match ls with
  | nil => nil
  | h :: t =>
      If fp h
      then filter_not fp t
      else h :: filter_not fp t
  end.

Lemma filter_not_nil_eq_list_filter (A: Type) (fp: A -> bool) (ls: list A):
   filter_not fp ls = List.filter (fun (vl: A) => ! (fp vl)) ls.
Proof.
  induction ls; auto.
  simpl.
  case_eq (fp a); intros Hfp; simpl; [rewrite If_l| rewrite If_r];
    rewrite ?IHls; auto.
Qed.  
  
Lemma filter_not_cons:
  forall (A : Type) (x : A) (l : list A) (P : A -> Prop),
       filter_not P (x :: l) =
         (If P x then filter_not P l else x :: filter_not P l).
Proof.
  intros; simpl; auto.
Qed.

Lemma filter_not_nil_eq_filter (A: Type) (fp: A -> Prop) (ls: list A):
   filter_not fp ls = filter (fun (vl: A) => ~ (fp vl)) ls.
Proof.
  induction ls; auto;
  rewrite filter_cons, filter_not_cons.
  case_eq (classicT (fp a));=> Hfp _.
  - rewrite If_r; auto.
  - rewrite If_l; auto.
    rewrite IHls; auto.
Qed.  
  
Lemma filter_not_nil:
  forall [A : Type] (P : A -> Prop), filter_not P nil = nil.
Proof.
  simpl; auto.
Qed.

Lemma filter_not_rev:
  forall [A : Type] (l : list A) (P : A -> Prop),
  filter_not P (rev l) = rev (filter_not P l).
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  rewrite filter_rev; auto.
Qed.  

Lemma LibList_length_filter_not:
  forall [A : Type] (l : list A) (P : A -> Prop),
  LibList.length (filter_not P l) <= LibList.length l.
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply LibList.length_filter.
Qed.

Lemma length_filter_not:
  forall [A : Type] (l : list A) (P : A -> Prop),
  length (filter_not P l) <= length l.
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply length_filter.
Qed.

Lemma mem_filter_not_eq:
  forall [A : Type] (x : A) (P : A -> Prop) (l : list A),
  mem x (filter_not P l) = (mem x l /\ ~ P x).
Proof.
  intros; rewrite filter_not_nil_eq_filter.
  apply mem_filter_eq.
Qed.

Lemma filter_not_app:
  forall [A : Type] (l1 l2 : list A) (P : A -> Prop),
  filter_not P (l1 ++ l2) = filter_not P l1 ++ filter_not P l2.
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  apply filter_app.
Qed.

Lemma filter_not_length_partition:
  forall [A : Type] (P : A -> Prop) (l : list A),
  length (filter_not (fun x : A => P x) l) +
  length (filter_not (fun x : A => ~ P x) l) <= length l.
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  apply filter_length_partition.
Qed.
  
Lemma filter_not_last:
  forall [A : Type] (x : A) (l : list A) (P : A -> Prop),
  filter_not P (l & x) = filter_not P l ++
                           (If P x then nil else x :: nil).
Proof.
  intros; rewrite !filter_not_nil_eq_filter.
  rewrite filter_last.
  repeat f_equal.
  case_eq (classicT (P x));=> Hfp _.
  - rewrite If_r; auto.
  - rewrite If_l; auto.
Qed.

