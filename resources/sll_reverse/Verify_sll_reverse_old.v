Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sll.
From Common Require Import Verify_arr.

From Common Require Import Tactics Utils Solver.

From ProofsSllReverse Require Import Sll_reverse_old_ml.

Lemma sll_reverse_f_spec :
  forall A `{EA: Enc A} (l: sll A) (ls: list A),
         SPEC (sll_reverse_f l)
         PRE (l ~> @SLL A EA ls)
         POST (fun (rl: sll A) => l ~> @SLL A EA ls \* rl ~> @SLL A EA (rev ls)) .
Proof using (All).
  xcf.
  xapp sll_nil_spec.
  xpullpure rl.
  xletopaque tmp Htmp.
  xapp (sll_iter_spec tmp l
         (fun (ls': list A) => rl ~> SLL (rev ls'))
         ls
       ). {
    introv Hls.
    xapp Htmp.
    xapp sll_push_spec.
    xmatch; xvals*.
    rew_list; auto.
  }
  xmatch; xvals*.
Qed.
