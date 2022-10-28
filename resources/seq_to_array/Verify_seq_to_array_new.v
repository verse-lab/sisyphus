Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_sseq.
From Common Require Import Verify_list.

From Common Require Import Tactics.
From Common Require Import Solver.
From Common Require Import Utils.

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
evar (ty_ls: Type).
evar (ls: ty_ls).
xapp (Common.Verify_sseq.fold_spec tmp (0, nil) s ?ls (fun '((i, acc): (int * list (A))) (x: A) => ((i + 1), x :: acc))).
sep_solve.
eauto.
clear ty_ls ls.
xdestruct len ls Hlenls.
rewrite list_fold_length_rev in Hlenls.
injection Hlenls; intros Hls Hlen.
case ls as [ | init rest] eqn:H_eqn.
- xmatch.
xvalemptyarr. { sis_generic_solver. }
- xmatch.
xalloc a data Hdata.
xletopaque idx Hidx.
xletopaque tmp0 Htmp0.
xapp (Common.Verify_list.list_fold_spec (tmp0) (idx) (rest)
        (fun (arg0: list (A)) (arg1: int) =>
           \[ (arg1 = ((idx - idx) + (idx - (length (arg0))))) ]  \*
             a ~> CFML.WPArray.Array (
               (drop ((length (arg0))) ((make ((length (rest))) (init)))) ++
                 (drop ((arg1 + len)) (((make ((length (rest))) (init)) ++ l)))))). {
  sis_generic_solver.
} { sis_generic_solver. } { sis_generic_solver. }
intros.
try xdestruct.
xvals*. { sis_generic_solver. }
Qed.
