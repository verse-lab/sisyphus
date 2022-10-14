Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_arr.

From Common Require Import Tactics Utils.

From ProofsArrayPartition Require Import Array_partition_new_ml.

Lemma array_partition_spec :
  forall (A : Type) `{EA : Enc A} (p: func) (a: array A)
         (pp : A -> bool) (l: list A),
  (forall a: A,
      SPEC (p a)
      PRE (\[])
      POST (fun (b: bool) => \[b = pp a])
  ) ->
  SPEC (partition p a)
  PRE (a ~> Array l)
  POST (fun '((a_t, a_f) : (loc * loc)) =>
          a ~> Array l \*
          a_t ~> Array (filter pp l) \*
            a_f ~> Array (filter_not pp l)
  ).
Proof using (All).
  xcf.
  xref a_f.
  xref a_t.
  xmatch.
  xletopaque tmp Htmp.
  xapp (array_iter_spec tmp a l (fun (ls: list A) =>
                                   a ~> Array l \*
                                   a_f ~~> filter_not pp (rev ls) \*
                                   a_t ~~> filter pp (rev ls)
       )). {
    intros v t r Htvr.
    lazymatch goal with
    | [ |- forall (Heq: _ = _), _] => intros Heq
    | [ |- forall (x: _), _] => intros x
    | [ H : Wpgen_body _ |- @Triple ?f ?r ?r2 ?P ?Q ] => apply H; clear H; xgo*
    end.
    Hint Database epic.
    lazymatch goal with
    | [ |- ?f _ = _] => idtac f
    end.

    eauto.

    intros v t r Htvr; apply Htmp; clear Htmp.
  }

Admitted.
