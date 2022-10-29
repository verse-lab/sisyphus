Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsSllPartition Require Import Sll_partition_old_ml.
                  
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
  xapp. intros s_t.
  xapp. intros s_f.
  xletopaque tmp Htmp.
  xapp (sll_fold_spec tmp (s_t, s_f) s
          (fun (ls: list A) '((s_t, s_f): sll A * sll A) =>
             s_t ~> SLL (filter pp (rev ls)) \*
             s_f ~> SLL (filter_not pp (rev ls))
       )). {
    intros [s_t' s_f'] t v r Htvr; apply Htmp; clear Htmp.
    sis_symexec; sis_generic_solver.
  }
  intros [s_t_res s_f_res].
  xmatch.
  xapp.
  xmatch.
  xapp.
  xmatch.
  xvals*. { sis_generic_solver. }
  { sis_generic_solver.  } { apply SLL_haffine. }
Qed.  
