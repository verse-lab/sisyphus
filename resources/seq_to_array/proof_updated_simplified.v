Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils_new.
From Proofs Require Import Seq_to_array_new.


Lemma to_array_spec : forall (A: Type) `{EA:Enc A} (l:list A) (s:func),
    SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun (a: loc) => a ~> Array l).
Proof using.
  xcf.
  xpullpure H1. 
  xpurefun f Hf using (fun (f: func) =>
     forall (i : credits) (acc : list A) (x : A),
       SPEC (f (i,acc) x)
       PRE (\[])
       POST (fun (res: int * list A) => \[res = (i + 1, x :: acc)])).
  xapp (fold_spec f (0, nil) s l (fun '((i,acc) : int * list A) (x: A) => (i + 1, x :: acc))); auto;
    first sep_solve.
  xdestruct len ls Hlenls.
  rewrite list_fold_length_rev in Hlenls.
  sep_split_tuple Hlenls Hlen Hls.
  case l as [| x xs] eqn:H.
  - xmatch_case_0.
    xvalemptyarr.
  - xmatch_case_1 with init rest Hrest.
    xalloc arr data Hdata.
    xletopaque idx Hidx.
    xletopaque ftmp Hftmp.
    xapp (list_fold_spec ftmp idx rest (fun (t: list A) (i: int) =>
        \[i = length (x :: xs) - length t - 2] \*
        arr ~> Array ((make (i + 1) init) ++ 
                                 drop (i + 1) (x :: xs))
         )). { admit. } { admit. } { admit. }
   intros i Hi.
   xdestruct.
   xvals.
   { admit. }
Admitted.
