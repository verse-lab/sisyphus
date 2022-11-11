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
xif as H_cond.
-
xvals.
{
sis_generic_solver.
}
-
xref result.
xletopaque tmp Htmp.
xapp (Common.Verify_combinators.while_downto_spec (((TLC.LibListZ.length (l)) - 1)) (0) (tmp) (fun (i: int) (res: bool) => \[ (res = (is_sorted ((drop (i) (l))))) ]  \* result ~~> (negb ((negb res)))
                                                                                                 \* a ~> Array l
     )).
{
  introv Hl. apply Htmp; clear Htmp.
  sis_symexec; sis_generic_solver.
}
{
sis_generic_solver.
}
{
sis_generic_solver.
}
intros.
xmatch.
xapp.
xvals.
{
  destruct x eqn:Heq; sis_generic_solver.
}
Qed.
