Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_stack Verify_list.

From Common Require Import Tactics Utils Solver.

From ProofsStackFilter Require Import Stack_filter_old_ml.

Lemma stack_filter_spec 
  {A: Type} `{EA: Enc A}
    (f: func) (s: stack A)
    (ls: list A) (fp: A -> bool):
    (forall (x: A),
        SPEC_PURE (f x)
        POST(fun (res: bool) => \[res = fp x])
    ) ->
    SPEC (stack_filter f s)
    PRE(s ~> Stack ls)
    POSTUNIT(s ~> Stack (filter fp ls)).
Proof using (All).
  xcf.
  xref acc.
  xletopaque tmp Htmp.
  xapp (stack_iter_spec tmp s (fun (ls: list A) => acc ~~> filter fp (rev ls))). {
    intros v t r Hvtr; apply Htmp; clear Htmp.
    sis_symexec; sis_generic_solver.
  }
  xmatch.
  xapp.
  xmatch.
  xapp.
  xletopaque tmp2 Htmp2.
  xapp (list_iter_spec tmp2 (filter fp (rev ls))
          (fun (ls: list A) => s ~> Stack (rev ls))). {
    sis_generic_solver.
  }
  xmatch.
  xvals*. { sis_generic_solver. }
Qed.
