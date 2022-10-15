Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Utils.
From Common Require Import Tree_ml.

(* logical tree *)
Inductive ltree A :=
| Lleaf : A -> ltree A
| Lnode : A -> ltree A -> ltree A -> ltree A.

Fixpoint Tree A `{EA: Enc A} (lt : ltree A)  (t: tree_ A) :=
  match lt with
  | Lleaf vl => t = Leaf vl
  | Lnode vl lt1 lt2 => exists t1 t2, (t = Node vl t1 t2) /\ Tree lt1 t1 /\ Tree lt2 t2
  end.

(* used for reasoning about tree combinators: [tree_iter] and [tree_fold] *)
Fixpoint tree_to_list {A} (lt: ltree A) :=
  match lt with
  | Lleaf vl => (vl :: nil)
  | Lnode vl t1 t2 => tree_to_list t1 ++ (vl :: nil) ++ tree_to_list t2
  end.

Inductive tree_sub A : ltree A -> ltree A -> Prop :=
  | tree_sub_1 : forall x T1 T2,
      tree_sub T1 (Lnode x T1 T2)
  | tree_sub_2 : forall x T1 T2,
      tree_sub T2 (Lnode x T1 T2).

Lemma tree_sub_wf : forall A, wf (@tree_sub A).
Proof using.
  intros A T. induction T; constructor; intros t' H; inversions~ H.
Qed.

(* size *)

Fixpoint lsize {A} (lt: ltree A) :=
  match lt with
  | Lleaf _ => 1
  | Lnode _ lt1 lt2 => 1 + lsize lt1 + lsize lt2
  end.

Lemma lsize_eq (A: Type) (t: ltree A):
  lsize t = length (tree_to_list t).
Proof.
  induction_wf IH: (tree_sub) t; [apply tree_sub_wf|].
  case t as [v|v l r] eqn: Ht.
  - simpl; rew_list; math.
  - simpl; rew_list.
   rewrite (IH l); try apply tree_sub_1.
   rewrite (IH r); try apply tree_sub_2.
   math.
Qed.

Lemma lsize_gt0 : forall A (lt : ltree A), 0 < lsize lt.
Proof. intros. induction lt; simpl; intros; try math. Qed.

Lemma size_spec: forall  A `{EA: Enc A} (lt: ltree A) (t: tree_ A),
  SPEC (size t)
       PRE (\[Tree lt t])
       POST (fun (s : int) => \[s = lsize lt]).
Proof.
  intros; gen t. induction lt; xcf; try auto.
  - intros; simpl; auto. xpullpure Hleaf. rewrite Hleaf.
    xmatch.
    xvals*.
  - intros; simpl. xpullpure H. destruct H as [t1 [t2 [Hnode [Ht1 Ht2]]]].
    rewrite Hnode; xmatch.
    xapp (IHlt2). apply Ht2.
    xapp (IHlt1). apply Ht1.
    xvals; auto.
Qed.

Arguments size_spec {A} {EA} lt t : rename.

Hint Extern 1 (RegisterSpec size) => Provide size_spec.

(* head *)
Fixpoint lhead {A} (lt: ltree A) :=
  match lt with
  | Lleaf vl => vl
  | Lnode vl _ _ => vl
  end.

Lemma head_spec : forall A `{EA: Enc A} (lt: ltree A) (t: tree_ A),
    SPEC (head t )
         PRE (\[Tree lt t])
         POST (fun (x : A) => \[x = lhead lt]).
Proof.
  intros; gen t. case lt; xcf; try auto.
  - intros; simpl; auto. xpullpure Hleaf. rewrite Hleaf. xmatch. xvals*.
  - simpl. xpullpure H. destruct H as [t1 [t2 [Hnode [Ht1 Ht2]]]].
    rewrite Hnode.
    xmatch.
    xvals*.
Qed.

Arguments head_spec {A} {EA} lt t : rename.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

(* Definition poptree A (x : A) (lt: ltree A) (ls: list (ltree A)) := *)
(*   match lt, ls with *)
(*   | Lleaf _, ls => Lleaf x :: ls *)
(*   | Lnode _ lt1 lt2, [lt2 :: lt1 :: ls] => Lnode x lt1 lt2 :: ls *)
(*   | _ => [] *)
(*   end *)


Lemma tree_iter_spec : forall A `{EA: Enc A},
  forall (f: func) (t: tree_ A)  (gt: ltree A)
    (* invariant *)
    (I : list A -> hprop),
    (* invariant condition *)
    (forall t v r,
        (tree_to_list gt = t ++ v :: r) ->
        SPEC (f v)
        PRE (I t)
        POSTUNIT (I (t & v)))
    ->
      SPEC (tree_iter f t)
           PRE (\[Tree gt t] \* I nil)
           POSTUNIT (I (tree_to_list gt)).
Proof.
  intros A EA.
  intros f t gt I Hf; gen t.

  cut (forall (l: list A) (r: list A) (lt: ltree A) (t: tree_ A),
        tree_to_list gt = l ++ tree_to_list lt ++ r ->
    SPEC (tree_iter f t)
           PRE (\[Tree lt t] \* I l)
           POSTUNIT (I (l ++ (tree_to_list lt)))).
  { intros Base_Spec t.
    pose proof (Base_Spec nil nil gt t) as Spec.
    rew_list in Spec.
    apply Spec; auto. }
  intros l r lt t; gen l r t.
  induction_wf IH: tree_sub lt; try (apply tree_sub_wf); intros.
  xcf.
  case lt as [vl | vl lt1 lt2] eqn: Hlt; simpl.
  - xpullpure Hleaf.
    xmatch. inversion TEMP as [Heq]; rewrite Heq in *.
    simpl in H; rew_list in H.
    xapp Hf; [exact H |].
    xsimpl*.
  - xpullpure Ht.
    destruct Ht as [t1 [t2 [Hnode [Ht1 Ht2]]]]; rewrite Hnode.
    xmatch.
    xapp (IH lt1). { apply tree_sub_1. } { rewrite H; simpl. f_equal. rew_list. f_equal. } { auto. }
    xapp (Hf). { rewrite H; simpl; rew_list; f_equal. }
    xapp (IH lt2). { apply tree_sub_2. } { rewrite H; simpl; rew_list; f_equal. } { auto. }
    rew_list.
    xsimpl*.
Qed.
Arguments tree_iter_spec {A} {EA} f lt t : rename.

Hint Extern 1 (RegisterSpec tree_iter) => Provide tree_iter_spec.

Lemma tree_fold_spec :  forall `{A: Type} `{Enc A} `{B: Type} `{Enc B} (f: val) (init : B) (lt: ltree A) (t: tree_ A) (fp: B -> A -> B),
     (forall acc v,
        SPEC_PURE (f acc v)
                  POST \[= fp acc v]) ->
      SPEC (tree_fold f init t)
           PRE \[Tree lt t]
           POST \[= List.fold_left fp (tree_to_list lt) init].
Proof.
  intros. gen t init.
  induction_wf IH: tree_sub lt; try (apply tree_sub_wf); intros.
  xcf.
  case lt as [vl | vl lt1 lt2]; simpl.
  - xpullpure Hleaf;  rewrite Hleaf.
    xmatch. xapp; simpl; xsimpl*.
  - xpullpure Hnode.
    destruct Hnode as [t1 [t2 [Hnode [Ht1 Ht2]]]]; rewrite Hnode.
    xmatch.
    xapp (IH lt1); (apply tree_sub_1 || auto).
    xapp.
    xapp (IH lt2); (apply tree_sub_2 || auto).
    xvals*.
    rewrite !fold_left_eq; rewrite !fold_left_app; auto.
Qed.
