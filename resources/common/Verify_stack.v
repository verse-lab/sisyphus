Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

(* Require Import Sseq_ml. *)
(* About Sseq_ml. *)

Require Import Stack_ml.
From Common Require Import Utils.
From Common Require Import Tactics.

Definition Stack {A: Type} `{EA: Enc A} (ls: list A) (s: loc) :=
  s ~~~> `{
      size' := length ls;
      elements' := ls
    }.

Definition stack := fun (A: Type) => loc.

Section Stack.
  Context {A: Type}.
  Context `{EA: Enc A}.
  
  Lemma Stack_unfold (ls: list A) (s: loc):
    s ~> Stack ls = s ~~~> `{ size' := length ls; elements' := ls }.
  Proof. unfold Stack; rewrite repr_eq; xsimpl*. Qed.

  Lemma stack_init_spec:
    SPEC(stack_init tt)
    PRE \[]
    POST (fun (s: stack A) => s ~> Stack (@nil A)).
  Proof.
    xcf.
    xapp.
    intros r.
    unfold Stack; rewrite (repr_eq (fun _ => _ ~~~> _)); xsimpl*.
  Qed.
  
  Lemma stack_size_spec (s: stack A) (ls: list A):
    SPEC(stack_size s)
    PRE (s ~> Stack ls)
    POST (fun (sz: int) => \[ sz = length ls ] \* s ~> Stack ls).
  Proof.
    xcf; auto.
    xchange Stack_unfold.
    xapp.
    xsimpl*.
  Qed.

  Lemma stack_pop_spec (s: stack A) (hd: A) (tl: list A):
    SPEC(stack_pop s)
    PRE (s ~> Stack (hd :: tl))
    POST (fun (res: A) => \[ res = hd ] \* s ~> Stack tl).
  Proof.
    xcf; auto.
    xchange Stack_unfold.
    xassert.
    xgo*; rew_list; math.
    xgo*.
    rewrite Stack_unfold; xsimpl*.
    rew_list; math.
  Qed.

  Lemma stack_push_spec (s: stack A) (hd: A) (tl: list A):
    SPEC(stack_push s hd)
    PRE (s ~> Stack tl)
    POST (fun (_: unit) => s ~> Stack (hd :: tl)).
  Proof.
    xcf; auto. 
    xchange Stack_unfold.
    xgo*.
    rewrite Stack_unfold.
    xgo*.
    rew_list; math.
  Qed.
  
  Lemma stack_clear_spec (s: stack A) (tl: list A):
    SPEC(stack_clear s)
    PRE (s ~> Stack tl)
    POST (fun (_: unit) => s ~> Stack (@nil A)).
  Proof.
    xcf; auto. 
    xchange Stack_unfold.
    xgo*.
  Qed.

  Lemma stack_iter_spec (f: func) (s: stack A)
     (I: list A -> hprop) (ls: list A) :
    (forall (v: A) (t r: list A),
        ls = t & v ++ r ->
        SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
    SPEC(stack_iter f s)
    PRE (s ~> Stack ls \* I nil)
    POST (fun (_: unit) => s ~> Stack ls \* I ls).
  Proof.
    intros Hf.
    xcf.
    xlet as;=> loop Hloop.
    assert (forall (t r: list A),
               ls = t ++ r ->
               SPEC (loop r)
               PRE (I t)
               POSTUNIT (I ls)). {
      intros t; remember (length t) as len; gen t.
      induction_wf IH: (upto (length ls)) len; intros t Hlen r Htr.
      apply Hloop; clear Hloop.
      case_eq r; [intros Hnil | intros rh rt Hrht].
      - xmatch. xvals*. subst; rew_list; xsimpl*.
      - xmatch.
        xapp (Hf rh t rt); try (subst; rew_list; auto; math).
        xapp (IH (len + 1)); try apply upto_intro; try (subst; rew_list; auto; math).
        xsimpl*.
    }
    xchange Stack_unfold.
    xapp.
    xapp; rew_list; auto.
    rewrite Stack_unfold; xsimpl*.
  Qed.
  Arguments stack_iter_spec f s I ls Hf : clear implicits.

  Lemma stack_drain_spec (f: func) (s: stack A)
    (I: list A -> hprop) (ls: list A):
    (forall (v: A) (t r: list A),
        ls = t & v ++ r ->
        SPEC (f v)
        PRE (I t)
        POST (fun (_ : unit) => I (t & v))) ->
    SPEC(stack_drain f s)
    PRE (s ~> Stack ls \* I nil)
    POST (fun (_: unit) => s ~> Stack (@nil A) \* I ls).
  Proof.
    intros Hf.
    cut (
        forall (t r : list A),
          ls = t ++ r ->
          SPEC (stack_drain f s)
            PRE s ~> @Stack A EA r \* I t
            POSTUNIT (s ~> @Stack A EA nil \* I ls)
      ). {
      intros H.
      apply (H nil ls); rew_list; auto.
    }
    intros t; remember (length t) as len; gen t.
    induction_wf IH: (upto (length ls)) len; intros t Hlen r Heq; xcf.
    xapp (stack_size_spec).
    case_eq r; [intros Hnil | intros rh rt Hreq].
    - rew_list; xif; try (intros; math).
      intros _.
      xvals*.
      subst; rew_list; xsimpl*.
    - rew_list; xif; try (intros; math).
      intros Hgt.
      xapp (stack_pop_spec).
      xapp (Hf rh t rt); try (subst; rew_list; auto; math).
      xapp (IH (len + 1)); try apply upto_intro; subst; rew_list; try math; auto.
      xsimpl*.
  Qed.
  Arguments stack_drain_spec f s I ls Hf : clear implicits.


End Stack.
