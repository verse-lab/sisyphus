Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Vec_ml.
From Common Require Import Utils.
From Common Require Import Tactics.

Lemma array_fill_spec: forall (A: Type) `{EA: Enc A} (i j: int) (x: A) (l m r : list A) data,
  i = length l -> j = length m ->
  SPEC (array_fill data i j x)
  PRE (data ~> Array (l ++ m ++ r))
  POSTUNIT (data ~> Array (l ++ make j x ++ r)).
Proof.
  intros A EA i j x l m r data Hi Hj; xcf.
  xlet.
  xlet as;=> loop Hloop.
  assert (forall (i: int),
             length l <= i <= length l + length m ->
             SPEC (loop i)
             PRE(data ~> Array (l ++ make (i - length l) x ++ drop (i - length l) m ++ r))
             POSTUNIT(
               data ~> Array (l ++ make (length m) x ++ r))
    ). {
    intros ind; induction_wf IH: (upto stop) ind; intros Hind.
    apply Hloop; clear Hloop.
    xif;=> cond.
    - xapp. {
        apply int_index_prove;
          rewrite <- ?length_eq;
          rew_list;
          rewrite ?length_make, ?length_drop;
          rew_list;
          try math.
      }
      xapp; try apply upto_intro; try math. {
        erewrite (@update_app_r _ _ (ind - length l)); eauto; try (subst; math).
        erewrite (@update_app_r _ _ 0); eauto; try (subst; rewrite length_make; math); try math.
        rewrite update_app_l; try (subst; rewrite length_drop; math).
        math_rewrite (ind + 1 - length l = ind - length l + 1).
        rewrite make_succ_r; try math.
        rew_list; rewrite <- app_cons_l.
        do 3 f_equal.
        rewrite drop_update_zero; try math.
        do 2 f_equal; math.
      }
      xsimpl*.
    - xvals*. {
        assert (Heq: ind = length l + length m) by math.
        rewrite Heq.
        math_rewrite (length l + length m - length l = length m).
        rewrite drop_at_length; rew_list; auto.
      }
  }
  xapp; try math. {
    subst; math_rewrite (length l - length l = 0); rewrite make_zero, drop_zero; rew_list; auto.
  }
  xsimpl*. { subst; auto. }
Qed.

Definition Vector A `{Enc A} (l: list A) (p: loc) : hprop :=
  \exists (data: loc) (D: list A) (G: list A),
     (* p points to the vector record w. size *)
      p ~> Record `{ vec' := data; size' := length l } \*
     (*  data points to an array modelled by D *)
      data ~> Array D \*
     (* D shares a prefix with l *)
      \[ D = l ++ G ].

Lemma Vector_unfold A `{Enc A} (l: list A) (p: loc) :
  p ~> Vector l =
  \exists (data: loc) (D: list A) (G: list A),
     (* p points to the vector record w. size *)
      p ~> Record `{ vec' := data; size' := length l } \*
     (*  data points to an array modelled by D *)
      data ~> Array D \*
     (* D shares a prefix with l *)
      \[ D = l ++ G ].
Proof. unfold Vector; rewrite repr_eq; xsimpl*. Qed.

Definition vector := fun (A: Type) => loc.

Section Vector.

  Context {A: Type}.
  Context `{EA: Enc A}.

  Lemma vec_size_spec (vt: vector A) (ls: list A):
    SPEC(vec_size vt)
    PRE(vt ~> Vector ls)
    POST(fun (res: int) => \[res = length ls] \* vt ~> Vector ls).
  Proof.
    xcf; eauto.
    xchange Vector_unfold;=> l D G Heq.
    xapp.
    rewrite Vector_unfold; xsimpl*.
  Qed.

  Lemma vec_get_spec `(IA: Inhab A) (vt: vector A) (i: int) (ls: list A):
    index ls i ->
    SPEC(vec_get vt i)
    PRE(vt ~> Vector ls)
    POST(fun (res: A) => \[res = ls[i]] \* vt ~> Vector ls).
  Proof.
    xcf; eauto.
    xchange Vector_unfold;=> l D G Heq.
    xapp.
    xapp. { subst; apply index_app_l; auto. }
    rewrite Vector_unfold; xsimpl*.
    rewrite Heq.
    rewrite read_app.
    rewrite index_eq_index_length, int_index_eq in H.
    rewrite If_l; try math; auto.
  Qed.

  Lemma vec_set_spec (vt: vector A) (i: int) (vl: A) (ls: list A):
    index ls i ->
    SPEC(vec_set vt i vl)
    PRE(vt ~> Vector ls)
    POSTUNIT(vt ~> Vector ls[i:=vl]).
  Proof.
    xcf; eauto.
    xchange Vector_unfold;=> l D G Heq.
    xapp.
    xapp. { subst; apply index_app_l; auto. }
    rewrite Vector_unfold; xsimpl*.
    rewrite length_update; auto.
    rewrite Heq.
    rewrite update_app_l; try math.
    eauto.
    rewrite index_eq_index_length, int_index_eq in H.
    math.
  Qed.

  Lemma vec_fill_spec (vt: vector A) (start len: int) (vl: A)
    (l m r: list A):
    start = length l ->
    len = length m ->
    SPEC(vec_fill vt start len vl)
    PRE(vt ~> Vector (l ++ m ++ r))
    POSTUNIT(vt ~> Vector (l ++ make (length m) vl ++ r)).
  Proof.
    xcf; eauto.
    xchange Vector_unfold;=> ol D G Heq.
    xapp.
    xapp (array_fill_spec). { eauto. } { eauto. } { subst; rew_list; auto. }
    rewrite Vector_unfold; xsimpl*.
    rew_list; rewrite length_make; math.
    subst; rew_list; eauto.
  Qed.
  
  Lemma vec_set_size_spec (vt: vector A) (len: int) (l r: list A):
    len = length l ->
    SPEC(vec_set_size vt len)
    PRE(vt ~> Vector (l ++ r))
    POSTUNIT(vt ~> Vector l).
  Proof.
    xcf; eauto.
    xchange Vector_unfold;=> ol D G Heq.
    xapp.
    rewrite Vector_unfold; xsimpl*.
    subst; rew_list; eauto.
  Qed.

End Vector.
