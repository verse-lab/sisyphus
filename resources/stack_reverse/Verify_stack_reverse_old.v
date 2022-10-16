Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_stack Verify_list.

From Common Require Import Tactics Utils Solver.

From ProofsStackReverse Require Import Stack_reverse_old_ml.

Lemma stack_reverse_spec 
  {A: Type} `{EA: Enc A} (s: stack A) (ls: list A) :
    SPEC (stack_reverse s)
    PRE(s ~> Stack ls)
    POSTUNIT(s ~> Stack (rev ls)).
Proof.
  xcf.
  xref buf.
  xletopaque tmp Htmp.
  xapp (@stack_drain_spec A EA tmp s
          (fun (ls: list A) =>
             buf ~~> rev ls
       )). {
    sis_solve_start; rew_list; auto.
  }
  xapp.
  xlet as;=> revls Hrevls.
  xletopaque tmp2 Htmp2.
  xapp (list_iter_spec tmp2 revls
          (fun (ls: list A) =>
             s ~> Stack (rev ls)
       )). {
    sis_solve_start; xapp (@stack_push_spec A EA); xgo*; rew_list; auto.
  }
  xmatch.
  xval*. {
    xsimpl*; subst; rewrite rev_rev; auto.
  }
Qed.
