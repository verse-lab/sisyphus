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
Proof.
  xcf.
  xapp (@queue_init_spec A EA). intros buf.
  xletopaque tmp Htmp.
  xapp (@stack_drain_spec A EA tmp s
          (fun (ls: list A) =>
             buf ~> Queue ls
       )). {
    sis_solve_start;
    xapp (@queue_enqueue_spec A EA); xgo*;
    rew_list; auto.
  }
  xmatch.
  xletopaque tmp2 Htmp2.
  xapp (@queue_iter_spec A EA tmp2 buf ls
          (fun (ls: list A) =>
             s ~> Stack (rev ls)
       )). {
    sis_solve_start; xapp (@stack_push_spec A EA); xgo*; rew_list; auto.
  }
  xmatch.
  xval*. {
    xsimpl*.
    unfold Queue; rewrite repr_eq.
    apply haffine_hexists; unfold haffine_post;intros.
    apply haffine_hexists; unfold haffine_post;intros.
    apply haffine_hstar. apply haffine_hpure.
    apply haffine_Record.
  }
Qed.
