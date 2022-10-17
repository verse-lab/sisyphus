Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

Lemma negb_eq_neg (b: bool):
  negb b = ! b.
Proof.
  case b; simpl; auto.
Qed.

Lemma negb_iff (b: bool) :
  b = false <-> ~ b.
Proof.
  case b; split; auto; intros H; try inversion H; auto.
  contradiction H; auto.
Qed.

Definition opt_of_bool (x: bool) := if x then Some tt else None.

Lemma opt_of_bool_none (b: bool) :
  None = opt_of_bool b -> b = false.
Proof. destruct b; simpl; auto; intros H; inversion H. Qed.  
Lemma opt_of_bool_some (b: bool) :
  Some tt = opt_of_bool b -> b = true.
Proof. destruct b; simpl; auto; intros H; inversion H. Qed.  

Lemma opt_of_bool_none_intro (b: bool) :
  b = false -> None = opt_of_bool b.
Proof. intros ->; simpl; auto. Qed.  
Lemma opt_of_bool_some_intro (b: bool) :
   b = true -> Some tt = opt_of_bool b.
Proof. intros ->; simpl; auto. Qed.  

Lemma is_some_opt_of_bool_eq (b: bool) :
  is_some (opt_of_bool b) = b.
Proof. case b; simpl; auto. Qed.

Fixpoint list_foldi_internal (A: Type) (B: Type)
  (i: int) (ls: list A) (init: B) (fp: int -> A -> B -> B) :=
  match ls with
  | nil => init
  | h :: t =>
      list_foldi_internal (i + 1) t (fp i h init) fp
  end.

Definition list_foldi (A: Type) (B: Type) (ls: list A) (init: B)
  (fp: int -> A -> B -> B) :=
  list_foldi_internal 0 ls init fp.

Global Hint Unfold list_foldi.

Lemma foldi_rcons (A: Type) (B: Type)
  (fp: int -> A -> B -> B) (acc: B) (rls: list A) (vl: A) (ls: list A):
  ls = rls & vl ->
  list_foldi ls acc fp = fp (length rls) vl (list_foldi rls acc fp).
Proof.
  unfold list_foldi.
  cut (forall t acc i vl,
          list_foldi_internal i (t & vl) acc fp =
            fp (i + length t) vl (list_foldi_internal i t acc fp)
      ). {
    intros H Hrls; rewrite Hrls.
    apply H.
  }
  clear.
  intros t; induction t as [ |  x xs IHxs ]; intros acc i vl.
  - rew_list; intros; subst; simpl; auto; f_equal; math.
  - rew_list; simpl. rewrite IHxs; f_equal; math.
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

Lemma drop_cons_unfold : forall A `{IA: Inhab A} (l: list A) i,
    0 <= i < length l ->
    drop i l = l[i] :: drop (i + 1) l.
Proof.
  intros A IA l; induction l.
  - intros i; rewrite length_nil; math.
  - intros i [Hgt Hlt].
    case (Zle_lt_or_eq _ _ Hgt).
    * intros Hgt1; rewrite length_cons in Hlt.
      math_rewrite (i = (i - 1) + 1).
      rewrite ! drop_cons; try math.
      rewrite IHl; try (split; math).
      rewrite read_cons_pos; try math.
      math_rewrite (i - 1 + 1 - 1 = i - 1).
      auto.
    * intros H; rewrite <- H.
      rewrite drop_cons; try math.
      rewrite !drop_zero.
      rewrite read_zero.
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

Lemma list_split_ith (A: Type) (IA: Inhab A) (l: list A) (i: int):
  0 <= i < length l ->
  l = take i l & l[i] ++ drop (i + 1) l.
Proof.
  intros Hlen.
  rewrite <- (@list_eq_take_app_drop _ (i + 1) l) at 1; try math.
  rewrite (take_pos_last IA); do 4 f_equal; try math.
  apply int_index_prove; math.
Qed.

Lemma drop_update_zero {A: Type} `{EA: Enc A}
            (i: int) (ls: list A) (vl: A)  :  
  0 <= i < length ls ->
  (drop i ls)[0:=vl] = vl :: drop (1 + i) ls.
Proof.
  gen i.
  induction ls as [ | x xs IHxs]; intros i Hlen.
  - rew_list in *; math.
  - case (Z.eqb_spec i 0); intros Heq0.
    + rewrite Heq0, drop_zero, update_zero.
      rewrite drop_cons_pos; try math.
      math_rewrite (1 + 0 - 1 = 0); rewrite drop_zero.
      auto.
    + rewrite drop_cons_pos; try math.
      rewrite IHxs; try (rew_list in *; math).
      f_equal.
      math_rewrite (1 + (i - 1) = i).
      math_rewrite (1 + i = i + 1).
      rewrite drop_cons; try math.
      auto.
Qed.      

Lemma fold_left_eq : forall A B (fp: B -> A -> B) (init: B) (ls : list A),
    List.fold_left fp ls init = fold_left (fun v acc => fp acc v) init ls.
Proof.
  intros. gen init. induction ls; intros; simpl; rew_list.
  - rewrite fold_left_nil; auto.
  - rewrite fold_left_cons; auto.
Qed.

Lemma make_app (A: Type) (v: A) (i j: int):
  i >= 0 -> j >= 0 ->
  make (i + j) v = make i v ++ make j v.
Proof.
  gen i.
  induction_wf IH: (downto 0) j.
  intros i Hi Hj.
  case (Z.eqb_spec j 0).
  - intros H0; rewrite H0, make_zero; rew_list; f_equal; math.
  - intros Hgt; assert (Hjgt0: j > 0) by math.
    math_rewrite (i + j = (i + (j - 1)) + 1).
    rewrite make_succ_r; try math.
    rewrite IH; try math; try (apply downto_intro; math).
    rew_list.
    assert (Hjlt0: j = (j - 1) + 1) by math.
    rewrite Hjlt0 at 2.
    rewrite make_succ_r; try math; auto.
Qed.

Lemma filter_eq: forall A (f: A -> bool) l,
    filter f l = List.filter f l.
Proof.
  intros A f l; induction l.
  - simpl; rewrite filter_nil; auto.
  - simpl; rewrite filter_cons.
    rewrite If_istrue; case_eq (f a); simpl; intros Hfa;
    rewrite IHl; auto.
Qed.

Lemma length_filter_take_leq_base : forall A (f: A -> bool) (l: list A) iv,
    0 <= iv ->
    length (filter f (take iv l)) <= iv.
Proof.
  intros.
  case_eq (Z.le_ge_cases iv (length l)); intros Hcmp _; try math.
  - assert (iv = length (take iv l)) as Hlt by (rewrite length_take; try math).
    rewrite Hlt at 2; apply length_filter.
  - apply (Z.le_trans _ (length l) _); try math.
    rewrite take_ge; try math.
    apply length_filter.
Qed.

Lemma length_filter_take_leq : forall A (f: A -> bool) (l: list A) iv, 
    length (filter f (take iv l)) <= length (filter f l).
Proof.
  intros A f l; induction l.
  - intros iv; rewrite take_nil; rewrite filter_nil; math.
  - intros iv; case_eq (Z.le_gt_cases 0 iv).
    * intros Hlv _; case_eq (Zle_lt_or_eq _ _ Hlv).
      ** intros Hpos _.
         rewrite take_cons_pos; try math.
         rewrite !filter_cons.
         rewrite !If_istrue.
         pose proof (IHl (iv - 1)) as IHli.
         case (f a); simpl; try rewrite ! length_cons; try math.
      ** intros H0 _; rewrite <- H0. rewrite take_zero; rewrite filter_nil;
           rewrite length_nil; try math.
    * intros Hneg _; rewrite take_neg; try math; rewrite filter_nil;
        rewrite length_nil; try math.
Qed.      

Lemma length_filter_succ: forall A `{IA: Inhab A} (f: A -> bool) (l: list A) (iv: int),
    0 <= iv  ->
    iv < length l ->
    length (filter (fun x : A => f x) (take (iv + 1) l)) =
      length (filter (fun x : A => f x) (take iv l)) + (if f l[iv] then 1 else 0).
Proof.
  intros A IA f l iv H0iv Hiv.
  rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
  rewrite filter_last.
  math_rewrite (iv + 1 - 1 = iv).
  rewrite If_istrue.
  case_eq (f l[iv]); intros Hliv; try rewrite length_last; rew_list; try math.
Qed.

Lemma take_filter_succ: forall A `{IA: Inhab A} (f: A -> bool) (l: list A) iv jv,
    f l[iv] -> jv < iv -> iv < length l ->
    jv = length (filter (fun x : A => f x) (take iv l)) ->
    take (jv + 1) (filter (fun x : A => f x) l) =
      take jv (filter (fun x : A => f x) l) & l[iv].
Proof.
  intros A IA f l iv jv Hfliv Hjviv Hiv Hjv.
  rewrite (@take_pos_last A IA _ (jv + 1)).
  - {
      case (@take_is_prefix A (iv + 1) l); intros l_suf Hlsuf.
      math_rewrite (jv + 1 - 1 = jv).
      rewrite Hlsuf at 2.
      rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
      rewrite filter_app; rewrite filter_last.
      math_rewrite (iv + 1 - 1 = iv). rewrite If_l; auto.
      rewrite read_app.
      rewrite If_l; try (rewrite length_last; rewrite Hjv; math).
      rewrite read_last_case.
      rewrite If_l; try (rewrite Hjv; math).
      auto.
    }
  - {
      apply int_index_prove; try math.
      rewrite <- length_eq. math_rewrite (jv + 1 - 1 = jv).
      rewrite Hjv.
      assert (0 <= iv) as Hivgt by math.
      case (@take_is_prefix A (iv + 1) l); intros l_suf Hlsuf.
      rewrite Hlsuf at 2.
      rewrite filter_app; rewrite length_app.
      rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
      math_rewrite (iv + 1 - 1 = iv).
      rewrite filter_last; rewrite If_l; auto; rewrite length_last.
      math.
    }
Qed.

Lemma drop_write_zero: forall A `{IA: Inhab A} (xs: list A) v i,
    0 <= i < length xs ->
    (drop i xs)[0:=v] =
      v :: drop (i + 1) xs.
Proof.
  intros A IA xs v i Hi.
  rewrite (@drop_cons_unfold A IA); try math.
  rewrite update_zero; auto.
Qed.

Lemma filter_take_propagate: forall A `{IA: Inhab A} (l: list A) (f: A -> bool) iv jv,
    f l[iv] -> 0 <= iv < length l ->
    jv = length (filter (fun x : A => f x) (take iv l)) ->
    (filter (fun x : A => f x) l)[jv] = l[iv].
Proof.
  introv Hfliv [Hlen_gt Hlen] Hjv.
  pose proof (length_filter_take_leq_base f l Hlen_gt) as Hjvlen.
  rewrite <- Hjv in Hjvlen.
  rewrite <- (@list_eq_take_app_drop _ iv l) at 1; try math.
  rewrite filter_app.
  rewrite read_app.
  rewrite If_r; try math.
  rewrite <- Hjv.
  math_rewrite (jv - jv = 0).
  rewrite (@drop_cons_unfold A IA); try (split; math).
  rewrite filter_cons; rewrite If_l; auto; rewrite read_zero.
  auto.
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

Lemma count_split (A B: Type) (ls: list (A * B)) (P: A -> Prop):
  length ls = count (fun '(vl, _) => P vl) ls + count (fun '(vl, _) => ~ P vl) ls.
Proof.
  induction ls as [| [l r]].
  - rewrite !count_nil; rew_list; math.
  - rewrite !count_cons; rew_list.
    case (classic (P l));=> Hp.
    + rewrite If_l, If_r; auto; rewrite IHls; math.
    + rewrite If_r, If_l; auto; rewrite IHls; math.
Qed.

Definition filter_first (A: Type) (k: int) (ls: list (int * A)) :=
  filter (fun '(k', _) => ~ (k = k')) ls.

Definition exists_first (A: Type) (k: int) (ls: list (int * A)) :=
  Exists (fun '(k', _) => k = k') ls.

Lemma drop_make_eq (A: Type) i j (vl: A) :
  0 <= i <= j ->
  drop i (make j vl) = make (j - i) vl.
Proof.
  intros Hij.
  apply (eq_of_extens (Inhab_of_val vl)).
  - rewrite length_drop; rewrite !length_make; try math.
  - intros ind Hind; generalize Hind; rewrite index_eq_index_length, int_index_eq; intros Hind'.
    rewrite length_drop_nonneg in *; rewrite !length_make in *; try math.
    rewrite read_drop;
      rewrite ?length_make; try math; try apply int_index_prove; try math.
    rewrite read_make; try apply int_index_prove; try math.
    rewrite read_make; try apply int_index_prove; try math.
    auto.
Qed.  

Lemma take_make_eq (A: Type) i j (vl: A) :
  0 <= i <= j ->
  take i (make j vl) = make i vl.
Proof.
  intros Hij.
  apply (eq_of_extens (Inhab_of_val vl)).
  - rewrite length_take; rewrite !length_make; try math.
  - intros ind Hind; generalize Hind; rewrite index_eq_index_length, int_index_eq; intros Hind'.
    rewrite length_take_nonneg in *; rewrite ?length_make in *; try math.
    rewrite read_take;
      rewrite ?length_make; try math; try apply int_index_prove; try math.
    rewrite read_make; try apply int_index_prove; try math.
    rewrite read_make; try apply int_index_prove; try math.
    auto.
Qed.  

Definition map2 (A: Type) (B: Type) (C: Type) (fp: A -> B -> C) (ls: list (A * B)) :=
  map (fun '(x,y) => fp x y) ls.

Lemma read_combine
  (A: Type) `{IA: Inhab A}
  (B: Type) `{IB: Inhab B}
  (xs: list A) (ys: list B) (i: int):
  length xs = length ys ->
  0 <= i < length xs ->
  (combine xs ys)[i] = (xs[i], ys[i]).
Proof.
  gen xs ys.
  induction_wf IH: (downto 0) i; intros xs ys Hlen Hi.
  case (Z.eqb_spec i 0) as [Hzero| Hnzero].
  - rewrite Hzero.
    case_eq xs; [intros Hnilx |intros x' xs' Heqx];
      (case_eq ys; [intros Hnily |intros y' xys' Heqy]);
    try (subst; rew_list in *; simpl; math).
    rewrite combine_cons, !read_zero; auto.
  - case_eq xs; [intros Hnilx |intros x' xs' Heqx];
      (case_eq ys; [intros Hnily |intros y' ys' Heqy]);
    try (subst; rew_list in *; simpl; math).
    rewrite combine_cons.
    math_rewrite (i = i - 1 + 1).
    rewrite !read_succ; try (subst; rew_list in *; math);
      try (rewrite length_eq, length_combine, <- length_eq;
           subst; rew_list in *; math).
    apply IH; try apply downto_intro; subst; rew_list in *;  try math.
Qed.

Lemma read_map2_combine
  (A: Type) `{IA: Inhab A}
  (B: Type) `{IB: Inhab B}
  (C: Type) `{IC: Inhab C}
  (fp: A -> B -> C) (xs: list A) (ys: list B) (i: int):
  length xs = length ys ->
  0 <= i < length xs ->
  (map2 fp (combine xs ys))[i] = fp xs[i] ys[i].
Proof.
  intros Heq Hlen; unfold map2.
  rewrite read_map; try (apply int_index_prove; rewrite ?length_combine; math).
  rewrite read_combine; auto.
Qed.

Fixpoint is_sorted_internal (x: int) (l: list int) :=
  match l with
  | nil => true
  | h :: t => (x <=? h) && is_sorted_internal h t
  end.

Definition is_sorted (l: list int) :=
  match l with
  | nil => true
  | h :: t => is_sorted_internal h t
  end.

Lemma is_sorted_cons (hd: int) (tl: list int) :
  is_sorted (hd :: tl) -> is_sorted tl.
Proof.
  case tl as [| hd2 tl]; simpl; auto; rewrite istrue_and_eq.
  intros []; auto.
Qed.

Lemma is_sorted_internal_gen hd (tl: list int):
  is_sorted_internal hd tl ->
  is_sorted tl.
Proof.
  destruct tl as [| tlh tll]; rew_list; try (intros; math).
  intros Hlen; simpl; auto.
  rew_list; simpl; rewrite istrue_and_eq; intros [_ ->]; auto.
Qed.


Lemma is_sorted_gen hd (tl: list int):
  length tl > 0 ->
  is_sorted tl ->
  hd <= tl[0] ->
  is_sorted (hd :: tl).
Proof.
  destruct tl as [| tlh tll]; rew_list; try (intros; math).
  intros Hlen.
  simpl; intros; subst; auto; rewrite H, istrue_and_eq; split; auto.
  case (Z.leb_spec0 hd tlh); auto; intros; try math.
Qed.

Lemma not_is_sorted_gen (l: list int) (i: int) :
  length l > 1 ->
  0 < i <= length l - 1 ->
  ~ l[i-1] <= l[i] ->
  ~ is_sorted l.
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
      rewrite (read_cons_pos Inhab_int hd); try math.
      apply H; auto; try (rewrite length_cons; math).
Qed.

Lemma is_sorted_last_elt (l: list int) :
  length l > 0 ->
  is_sorted (drop (length l - 1) l).
Proof.
  case l as [| fst tl]; rew_list; intros; try math; auto.
  gen fst H.
  induction tl as [| x xs IHxs]; rew_list; intros fst.
  - intros; math_rewrite (1 + 0 - 1 = 0); rewrite drop_zero; simpl; auto.
  - intros Hgt; math_rewrite (1 + (1 + length xs) - 1 = length xs + 1).
    rewrite drop_cons; try math.
    math_rewrite (1 + length xs - 1 = length xs)  in IHxs.
    eapply IHxs; auto; math.
Qed.

Lemma is_sorted_app_l (t r: list int) :
  is_sorted t = false ->
  is_sorted (t ++ r) = false.
Proof.
  case t; simpl; intros; try (inversion H; auto; math).
  rew_list; simpl.
  gen z H; induction l as [| x xs IHxs]; simpl.
  - intros z H; inversion H; auto.
  - rew_list; simpl; intros z H; rewrite <- if_else_false in *.
    destruct (Z.leb z x).
    + apply IHxs; auto.
    + auto.
Qed.      

Lemma is_sorted_app_r (t r: list int) :
  is_sorted r = false ->
  is_sorted (t ++ r) = false.
Proof.
  case t; rew_list; simpl; auto; intros t_hd t_tl; clear t; rew_list; simpl.
  gen r t_hd; induction t_tl.
  - intros r t_hd; rew_list.
    gen t_hd; induction r as [| rh rt IHr]; intros t_hd; simpl; intros H; auto.
    rewrite H; case (t_hd <=? rh); simpl; auto.
  - intros r t_hd Hr; rew_list; simpl; rewrite IHt_tl; auto.
    case (t_hd <=? a); auto.
Qed.      

