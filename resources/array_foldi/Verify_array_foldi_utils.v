Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From ProofsArrayFoldi Require Import Common_ml.

Fixpoint foldi_pure (A B: Type) f i (init: A) (ls: list B) :=
  match ls with
  | nil => init
  | h :: t => foldi_pure f (i + 1) (f i init h) t
  end.

Lemma foldi_pure_last (A B: Type) f i (init: A) (ls: list B) (vl: B):
  foldi_pure f i init (ls & vl) =
  f (i + LibListZ.length ls) (foldi_pure f i init ls) vl.
Proof.
  gen i vl init. induction ls.
  - intros i vl init; rewrite app_nil_l, length_nil, Z.add_0_r; simpl; auto.
  - intros i vl init. rewrite app_cons_l; simpl.
    rewrite IHls.
    rewrite length_cons.
    f_equal; math.
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
