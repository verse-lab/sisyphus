Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver Verify_opt.

From ProofsArrayExists Require Import Array_exists_new_ml.

Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = List.existsb fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec unit 0 (length l) tmp
          (fun (i: int) (b: option unit) =>
             \[b = opt_of_bool (List.existsb fp (take i l))] \*
               a ~> Array l)
       ). {
    sis_generic_solver.
  }
  { sis_generic_solver. }
  { sis_generic_solver. }
  intros fin i_b Hres Hexists.
  xapp.
  xvals*. {
    destruct fin; destruct Hres as [Hlen Himpl]; simpl in *; try destruct u;
    sis_generic_solver.
  }
Qed.
