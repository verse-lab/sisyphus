Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver.
From Common Require Import Verify_opt.

From ProofsArrayFindi Require Import Array_findi_new_ml.

Lemma array_findi_spec :
  forall (A : Type) `{EA : Enc A}
         (a : array A) (f : func) (l : list A) (fp: int -> A -> bool),
    (forall (i: int)(a: A), 0 <= i < length l ->
        SPEC_PURE (f i a)
         POST (fun (b: bool) => \[b = fp i a])) ->
  SPEC (findi a f)
  PRE (a ~> Array l)
  POST (fun (b : option (int * A)) =>
          \[b = list_findi fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as Hcond.
  - xvals. { sis_generic_solver. }
  - xinhab.
    xref found.
    xref idx.
    xapp. { sis_generic_solver. }
    xref value.
    xletopaque tmp Htmp.
    xapp (while_upto_spec 0 (length l) tmp
            (fun (i: int) (b: bool) =>
               \[b = negb (is_some (list_findi fp (take i l)))] \*
               a ~> Array l \*
               value ~~> option_value_snd l[0] (list_findi fp (take i l)) \*
               idx ~~> option_value_fst 0 (list_findi fp (take i l)) \*
               found ~~> negb b
         )). { sis_generic_solver. } 
      { sis_generic_solver.  }
      { sis_generic_solver. }
    intros res i_b Hres Hexists.
    xmatch.
    xapp.
    xif as Hlcond.
    + xapp.
      xapp.
      xvals*. {
        destruct Hres as [Hlen Himpl].
        sis_generic_solver.
        rewrite <- (@list_eq_take_app_drop _ i_b l) at 4; try math.
        rewrite !findi_unfold, findi_app_l in *; auto; simpl.
        gen Hexists.
        case (list_findi_internal 0 fp (take i_b l)) as [[p1 p2] |]; simpl; intros; auto.
        inversion Hexists.
      }
    + xvals*. {
        destruct Hres as [Hlen Himpl].
        sis_generic_solver.
      }
Qed.
