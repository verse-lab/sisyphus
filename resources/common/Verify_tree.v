Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Utils Tactics.
From Common Require Import Tree_ml.

(* used for reasoning about tree combinators: [tree_iter] and [tree_fold] *)
Fixpoint tol (A: Type) (lt: tree_ A) :=
  match lt with
  | Leaf vl => (vl :: nil)
  | Node vl t1 t2 => tol t1 ++ (vl :: nil) ++ tol t2
  end.

Inductive tree_sub A : tree_ A -> tree_ A -> Prop :=
  | tree_sub_1 : forall x T1 T2,
      tree_sub T1 (Node x T1 T2)
  | tree_sub_2 : forall x T1 T2,
      tree_sub T2 (Node x T1 T2).

Lemma tree_sub_wf : forall A, wf (@tree_sub A).
Proof using.
  intros A T. induction T; constructor; intros t' H; inversions~ H.
Qed.

(* size *)
Fixpoint tsize (A: Type) (lt: tree_ A) :=
  match lt with
  | Leaf _ => 1
  | Node _ lt1 lt2 => 1 + tsize lt1 + tsize lt2
  end.

Lemma tree_size_eq (A: Type) (t: tree_ A):
  tsize t = length (tol t).
Proof.
  induction_wf IH: (tree_sub) t; [apply tree_sub_wf|].
  case t as [v|v l r] eqn: Ht.
  - simpl; rew_list; math.
  - simpl; rew_list.
   rewrite (IH l); try apply tree_sub_1.
   rewrite (IH r); try apply tree_sub_2.
   math.
Qed.

Lemma tree_size_ge0 : forall A (lt : tree_ A), 0 <= tsize lt.
Proof. intros. induction lt; simpl; intros; try math. Qed.

Lemma tree_size_gt0 : forall A (lt : tree_ A), 0 < tsize lt.
Proof. intros. induction lt; simpl; intros; try math. Qed.

#[export] Hint Resolve tree_size_ge0: size_lemmas.
#[export] Hint Resolve tree_size_gt0: size_lemmas.

Lemma tree_size_spec: forall {A} `{EA: Enc A} (t: tree_ A),
  SPEC_PURE (tree_size t)
  POST (fun (s : int) => \[s = tsize t]).
Proof.
  intros; gen t. induction t; xcf; try auto.
  - xmatch.
    xvals*.
  - xmatch.
    xapp.
    xapp (IHt1).
    xvals; auto.
Qed.
(* Arguments tree_size_spec {A} {EA} t : rename. *)
Hint Extern 1 (RegisterSpec tree_size) => Provide tree_size_spec.

(* head *)
Definition thead A (t: tree_ A) :=
  match t with
  | Leaf vl => vl
  | Node vl _ _ => vl
  end.
Arguments thead A t : rename.

Lemma tree_head_spec : forall {A} `{EA: Enc A} (t: tree_ A),
    SPEC_PURE (tree_head t)
    POST (fun (x : A) => \[x = thead t]).
Proof.
  intros. case t; xcf; xmatch; xvals*.
Qed.
Arguments tree_head_spec {A} {EA} t : rename.
Hint Extern 1 (RegisterSpec tree_head) => Provide tree_head_spec.

Lemma tree_iter_spec : forall A `{EA: Enc A} (f: func) (gt: tree_ A)
    (* invariant *)
    (I : list A -> hprop),
    (* invariant condition *)
    (forall t v r,
        (tol gt = t ++ v :: r) ->
        SPEC (f v)
        PRE (I t)
        POSTUNIT (I (t & v)))
    ->
      SPEC (tree_iter f gt)
           PRE (I nil)
           POSTUNIT (I (tol gt)).
Proof.
  intros A EA f gt I Hf.
  cut (forall (t: list A) (r: list A) (lt: tree_ A),
        tol gt = t ++ tol lt ++ r ->
    SPEC (tree_iter f lt)
           PRE (I t)
           POSTUNIT (I (t ++ (tol lt)))).
  { intros Base_Spec.
    pose proof (Base_Spec nil nil gt) as Spec.
    rew_list in Spec.
    apply Spec; auto. }
  intros t r lt; gen t r.
  induction_wf IH: tree_sub lt; try (apply tree_sub_wf); intros.
  xcf.
  case lt as [vl | vl lt1 lt2] eqn: Hlt; simpl.
  - xmatch.
    xapp (Hf t vl r). { rewrite H; simpl; rew_list; auto. }
    xsimpl*.
  - xmatch.
    xapp (IH lt1). { apply tree_sub_1. } { rewrite H; simpl. f_equal. rew_list. f_equal. }
    xapp (Hf). { rewrite H; simpl; rew_list; f_equal. }
    xapp (IH lt2). { apply tree_sub_2. } { rewrite H; simpl; rew_list; f_equal. }
    rew_list.
    xsimpl*.
Qed.
Arguments tree_iter_spec {A} {EA} f lt t : rename.
Hint Extern 1 (RegisterSpec tree_iter) => Provide tree_iter_spec.

Lemma tree_fold_spec :  forall {A: Type} `{Enc A} {B: Type} `{Enc B}
                               (f: val) (init : B) (t: tree_ A) (fp: B -> A -> B),
     (forall acc v,
        SPEC_PURE (f acc v)
                  POST \[= fp acc v]) ->
      SPEC_PURE (tree_fold f init t)
        POST \[= List.fold_left fp (tol t) init].
Proof.
  intros. gen init.
  induction_wf IH: tree_sub t; try (apply tree_sub_wf); intros.
  xcf.
  case t as [vl | vl lt1 lt2]; simpl.
  - xmatch.
    xapp.
    xsimpl*.
  - xmatch.
    xapp (IH lt1); [apply tree_sub_1 | auto].
    xapp.
    xapp (IH lt2); [apply tree_sub_2 | auto].
    xvals*.
    rewrite !fold_left_eq; rewrite !fold_left_app; auto.
Qed.
Arguments tree_fold_spec {A} {EA} {B} {EB} f init t fp : rename.
Hint Extern 1 (RegisterSpec tree_fold) => Provide tree_fold_spec.
