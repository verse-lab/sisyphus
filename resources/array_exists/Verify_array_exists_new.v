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
xapp (Common.Verify_combinators.until_upto_spec (unit) (0) ((TLC.LibListZ.length (l))) (tmp)
        (fun (i: int) (res: (option (unit))) => \[ (res = (opt_of_bool ((existsb (fp) ((take (i) (l))))))) ]
    (* NOTE: ADDED a ~> Array l MANUALLY *)
    \* a ~> Array l )).
{
  sis_generic_solver.
}
{
sis_generic_solver.
}
{
sis_generic_solver.
}
intros result Hresult.
intros.
xapp.
xvals.
{
  sis_generic_solver.
  unfold existsb in *.
  destruct (List.existsb fp (take Hresult l)) eqn:Hb; sis_generic_solver.
}
Qed.
