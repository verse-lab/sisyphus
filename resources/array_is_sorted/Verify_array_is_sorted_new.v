Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.
From Common Require Import Tactics Solver Utils.

From ProofsArrayIsSorted Require Import Array_is_sorted_new_ml.


Lemma array_is_sorted_spec :
  forall (a : array int) (l : list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as cond.
  - xvals*. { sis_generic_solver. }
  - xref result.
    xletopaque tmp Htmp.
    xapp (while_downto_spec (length l - 1) 0 tmp
            (fun (i: int) (b: bool) =>
               \[ b = is_sorted (drop i l) ] \*
                 result ~~> b \*
                 a ~> Array l)
         ). {
      intros i Hi; apply Htmp; clear Htmp.
      sis_symexec; sis_generic_solver.
    } { sis_generic_solver. } { sis_generic_solver. }
    intros term i Hcond Heq.
    xmatch.
    xapp.
    xvals*. { destruct term; sis_generic_solver. }
Qed.
