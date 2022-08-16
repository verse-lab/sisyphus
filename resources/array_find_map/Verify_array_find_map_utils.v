Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFindMap Require Import Common_ml.
(* From ProofsArrayFind Require Import array_find_old_ml. *)

Fixpoint list_find_map (A B: Type) (f:  A -> option B) (ls: list A)  :=
  match ls with
  | nil => None
  | h :: t =>
      match f h with
      | Some res => Some res
      | None =>
          list_find_map f t
      end
  end.

Lemma length_find_propagate:
  forall (A B: Type) (fp: A -> option B) (t: list A) (v: A),
    list_find_map fp t = None ->
    fp v = None ->
    list_find_map fp (t & v) = None.
Proof.
  intros A B fp.
  induction t.
  - intros v; rewrite app_nil_l; simpl; intros _ ->; auto.
  - intros v.
    rewrite app_cons_l; intros Hfind Hfp.
    assert (Hfp0: fp a = None). {
      case_eq (fp a); [intros res Heq|];
      try (simpl in Hfind; rewrite Heq in Hfind; inversion Hfind).
      auto.
    }
    simpl.
    rewrite Hfp0.
    apply IHt.
    + simpl in Hfind; rewrite Hfp0 in Hfind; auto.
    + gen Hfp. auto. 
Qed.      

Lemma length_find_final:
  forall (A B: Type) fp (l t r: list A) (v: A) (res: B),
    l = t ++ v :: r ->
    list_find_map fp t = None ->
    fp v = Some res ->
    list_find_map fp l = Some res.
Proof.
  intros A B fp.
  intros l t; gen l.
  induction t.
  - intros l r v res; rewrite app_nil_l; intros -> _;
    intros Hfp; simpl; rewrite Hfp; auto.
  - intros l r v res.
    rewrite app_cons_l; intros Hl Hfind.
    assert (Hfp0: fp a = None). {
      case_eq (fp a); [intros res' Heq|];
        try (simpl in Hfind; rewrite Heq in Hfind; inversion Hfind).
      auto.
    }
    intros Hfp.
    rewrite Hl; simpl; rewrite Hfp0.
    rewrite (IHt (t ++ v :: r) r v res); auto.
    gen Hfind; simpl; rewrite Hfp0; auto.
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

