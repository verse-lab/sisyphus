Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Utils Solver Tactics. 

From Common Require Import Verify_combinators. 
From Common Require Import Verify_list. 

From ProofsArrayOfRevList Require Import Array_of_rev_list_old_ml.
    
Lemma array_of_rev_list : forall A `{EA:Enc A} (l:list A),
  SPEC (array_of_rev_list l)
    PRE (\[])
    POST (fun a => a ~> Array (rev l)).
Proof using (All).
  xcf.
  case l as [ | x l'] eqn: H.
  - xmatch_case_0.
    xvalemptyarr.
  - xmatch.
    xletopaque len Hlen.
    xalloc arr data Hdata.
    xref r.
    xletopaque tmp Htmp.
    xapp (for_downto_spec (len - 2) 0 tmp
            (fun (i: int) =>
               r ~> Ref (drop (len - (i + 1)) l) \*
                 arr ~> Array (take (i + 1) data ++ rev (take (len - (i + 1)) l)))).
    { sis_generic_solver. }
    { sis_generic_solver. }
    { sis_generic_solver. } { sis_generic_solver. }
    xunit.
    xsimpl.
    { sis_generic_solver. }
Qed.
