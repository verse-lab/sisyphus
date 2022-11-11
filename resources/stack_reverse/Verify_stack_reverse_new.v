Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_stack Verify_queue.

From Common Require Import Tactics Utils Solver.

From ProofsStackReverse Require Import Stack_reverse_new_ml.

Lemma stack_reverse_spec
  {A: Type} `{EA: Enc A} (s: stack A) (ls: list A) :
    SPEC (stack_reverse s)
    PRE(s ~> Stack ls)
    POSTUNIT(s ~> Stack (rev ls)).
Proof using (All).
xcf.
xapp.
intro buf.
xletopaque tmp Htmp.
xapp (Common.Verify_stack.stack_drain_spec (tmp) (s) (fun (arg0: list (A)) =>  buf ~> Common.Verify_queue.Queue (arg0))).
{
sis_generic_solver.
}
xmatch.
xletopaque tmp0 Htmp0.
xapp (Common.Verify_queue.queue_iter_spec (tmp0) (buf) (fun (arg0: list (A)) =>  s ~> Common.Verify_stack.Stack ((rev (arg0))))).
{
sis_generic_solver.
}
xmatch.
xvals.
{ apply queue_affine. }
Qed.
