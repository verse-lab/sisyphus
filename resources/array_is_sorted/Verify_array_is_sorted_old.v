Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Tactics Solver Utils.
From Common Require Import Verify_combinators Verify_opt.

From ProofsArrayIsSorted Require Import Array_is_sorted_old_ml.

Lemma array_is_sorted_spec :
  forall (a : array int) (l : list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as cond.
  - xvals*. { sis_list_solver. }
  - xletopaque tmp Htmp.
    xapp (until_downto_spec unit (length l - 1) 0 tmp
            (fun (i: int) (b: option unit) =>
               \[b = opt_of_bool (negb (is_sorted (drop i l)))] \*
                 a ~> Array l)
         ). { sis_generic_solver. } { sis_generic_solver. } { sis_generic_solver. }
    intros term i Hcond Heq.
    xapp.
    xvals*. {
      destruct ((is_sorted (drop i l))) eqn: Heqv;
        sis_generic_solver.
    }
Qed.
