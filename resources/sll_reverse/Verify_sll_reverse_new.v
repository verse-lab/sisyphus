Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsSllReverse Require Import Sll_reverse_new_ml.

Lemma sll_reverse_f_spec :
  forall A `{EA: Enc A} (l: sll A) (ls: list A),
         SPEC (sll_reverse_f l)
         PRE (l ~> @SLL A EA ls)
         POST (fun (rl: sll A) => l ~> @SLL A EA ls \* rl ~> @SLL A EA (rev ls)) .
Proof using (All).
  xcf.
  xapp sll_nil_spec.
  intros init.
  xletopaque tmp Htmp.
  About sll_fold_spec.
  xapp (sll_fold_spec tmp init l
         (fun (ls': list A) (rl': sll A) => rl' ~> SLL (rev ls'))
         ls
       ). {
    introv Hls.
    xapp Htmp.
    xapp sll_cons_spec; intros rl; xvals*.
    rew_list; auto.
  }
  intros rl; xvals*.
Qed.
