Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsSllPartition Require Import Sll_partition_new_ml.

Lemma sll_partition_spec :
  forall (A : Type) `{EA : Enc A} (p: func) (s : sll A)
         (pp: A -> bool) (ls: list A),
    (forall (x: A),
        SPEC_PURE (p x)
        POST (fun (b: bool) => \[b = pp x])
    ) ->
  SPEC (sll_partition p s)
  PRE (s ~> SLL ls)
  POST (fun '((l,r) : sll A * sll A) =>
          l ~> SLL (filter pp ls) \*
            r ~> SLL (filter_not pp ls)
  ).
Proof using (All).
xcf.
xapp.
xmatch.
xapp.
intro sll_yes.
xapp.
intro sll_no.
xletopaque tmp Htmp.
xapp (Common.Verify_sll.sll_iter_drain_spec (tmp) (s) (fun (arg0: list (A)) =>  sll_no ~> Common.Verify_sll.SLL ((filter_not (pp) ((rev (arg0))))) \* sll_yes ~> Common.Verify_sll.SLL ((filter (pp) ((rev (arg0))))))).
{
sis_generic_solver.
}
xmatch.
xvals.
{
sis_generic_solver.
}
{
sis_generic_solver.
}
Qed.
