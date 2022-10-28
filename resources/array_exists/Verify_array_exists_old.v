Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.

From ProofsArrayExists Require Import Array_exists_old_ml.

Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = existsb fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xref result.
  xletopaque tmp Htmp.
  xapp (while_upto_spec 0 (length l) tmp
           (fun (i: int) (b: bool) => \[b = negb (existsb fp (take i l))] \*
                         result ~~> (existsb fp (take i l)) \*
                         a ~> Array l)
       ). { sis_generic_solver. }
  { sis_generic_solver. }
  { sis_generic_solver. }
  intros fin i_b Hind Hexists.
  xmatch.
  xapp.
  xvals*. {
    destruct fin; destruct Hind as [Hlen Himpl];
      sis_generic_solver.
  }
Qed.
