Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFind Require Import Common_ml.
(* From ProofsArrayFind Require Import array_find_old_ml. *)

Fixpoint list_findi (A: Type) (f: int -> A -> bool) (n: int) (ls: list A)  :=
  match ls with
  | nil => None
  | h :: t =>
      if f n h
      then Some (n, h)
      else list_findi f (n + 1) t
  end.

Lemma length_find_propagate:
  forall (A: Type) fp (t: list A) (v: A),
    list_findi fp 0 t = None ->
    fp (LibListZ.length t) v = false ->
    list_findi fp 0 (t & v) = None.
Proof.
  intros A fp.
  intros t.
  math_rewrite (LibListZ.length t = 0 + LibListZ.length t).
  generalize 0.
  induction t.
  - intros b0 v; rewrite app_nil_l, length_nil, Z.add_0_r; simpl; intros _ ->; auto.
  - intros b0 v.
    rewrite app_cons_l; intros Hfind Hfp.
    assert (Hfp0: fp b0 a = false). {
      case_eq (fp b0 a); intros Heq;
        try (simpl in Hfind; rewrite Heq in Hfind; inversion Hfind).
      auto.
    }
    simpl.
    rewrite Hfp0.
    apply IHt.
    + simpl in Hfind; rewrite Hfp0 in Hfind; auto.
    + gen Hfp. rew_list. math_rewrite ((b0 + (1 + LibListZ.length t)) = (b0 + 1 + LibListZ.length t)); auto.
Qed.      

Lemma length_find_final:
  forall (A: Type) fp (l t r: list A) (v: A),
    l = t ++ v :: r ->
    list_findi fp 0 t = None ->
    fp (LibListZ.length t) v = true ->
    list_findi fp 0 l = Some (LibListZ.length t, v).
Proof.
  intros A fp.
  intros l t; gen l.
  math_rewrite (LibListZ.length t = 0 + LibListZ.length t).
  generalize 0.
  induction t.
  - intros b0 l r v; rewrite app_nil_l; intros -> _.
    rewrite LibListZ.length_nil, Z.add_0_r; intros Hfp; simpl; rewrite Hfp; auto.
  - intros b0 l r v.
    rewrite app_cons_l; intros Hl Hfind.
    assert (Hfp0: fp b0 a = false). {
      case_eq (fp b0 a); intros Heq;
        try (simpl in Hfind; rewrite Heq in Hfind; inversion Hfind).
      auto.
    }
    rew_list.
    intros Hfp.
    rewrite Hl; simpl; rewrite Hfp0.
    rewrite (IHt (b0 + 1) (t ++ v :: r) r v); auto.
    rew_list; do 2 f_equal; math.
    gen Hfind; simpl; rewrite Hfp0; auto.
    math_rewrite ((b0 + 1 + LibListZ.length t) = (b0 + (1 + LibListZ.length t))).
    auto.
Qed.

Lemma length_spec : forall A `{EA:Enc A} (a:loc) (l:list A),
    SPEC (Common_ml.length a)
   PRE(\[])
   INV (a ~> Array l) 
   POST (fun (ln: int) => \[ln = LibListZ.length l]).
Proof using.
  intros A EA a l.
  xcf.
  xapp.
  xsimpl*.
Qed.

Lemma index_cons (A: Type) `{IA: Inhab A} (ls: list A):
  LibListZ.length ls > 0 -> ls = ls[0] :: drop 1 ls.
Proof.
  case ls.
  - rewrite LibListZ.length_nil; math.
  - intros hd tl; rewrite read_zero.
    math_rewrite (1 = 0 + 1).
    rewrite drop_cons, drop_zero; try math; auto.
Qed.

