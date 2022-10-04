Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.
Lemma to_array_spec :
  forall (A : Type) `{EA : Enc A} (l : list A) (s : func) (v : loc),
  SPEC (to_array s)
  PRE \[LSeq l s]
  POST (fun a : loc => a ~> Array l).
Proof using (All).
xcf.
xpullpure H1.
xletopaque tmp Htmp.
evar ( ty_ls : Type ).
evar ( ls : ty_ls ).
xapp
 (Proofs.Verify_seq_to_array_utils.fold_spec tmp (0, nil) s ?ls
    (fun '((i, acc) : int * list A) (x : A) => (i + 1, x :: acc))).
sep_solve.
eauto.
clear ty_ls ls.
xdestruct len ls Hlenls.
(rewrite list_fold_length_rev in Hlenls).
(injection Hlenls; intros Hls Hlen).
(destruct ls as [| init rest] eqn:H_eqn).
-
xmatch.
xvalemptyarr.
{
admit.
}
-
xmatch.
xalloc a data Hdata.
xletopaque idx Hidx.
xletopaque tmp0 Htmp0.
xapp
 (Proofs.Verify_seq_to_array_utils.list_fold_spec tmp0 idx rest
    (fun (arg0 : list A) (arg1 : int) =>
     \[arg1 = length rest - length l + (length rest - length arg0)] \*
     a ~> CFML.WPArray.Array (make (1 + arg1) init ++ drop (1 + arg1) l))).
{ admit. } {  admit. } { admit. }
(intros unused Hunused).
try xdestruct.
xvals.
{ admit. }
Admitted.
