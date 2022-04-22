Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_new_ml.


Lemma to_array_spec : forall (A: Type) `{EA:Enc A} (l:list A) (s:func),
    SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun (a: loc) => a ~> Array l).
Proof using.
  xcf.
  xpullpure H1.
  xletopaque f Hf.
  xapp (fold_spec f (0, nil) s l (fun '((i,acc) : int * list A) (x: A) => (i + 1, x :: acc))); auto;
    first sep_solve.
  xdestruct len ls Hlenls.
  rewrite list_fold_length_rev in Hlenls.
  sep_split_tuple Hlenls Hlen Hls.
  case (rev l) as [| init rest] eqn:H.
  - xmatch_case_0.
    xvalemptyarr. { admit. }
  - xmatch.
    xalloc arr data Hdata.
    xletopaque idx Hidx.
    xletopaque ftmp Hftmp.
    xapp (list_fold_spec ftmp idx rest (fun (t: list A) (i: int) =>
        \[i = length l - length t - 2] \*
        arr ~> Array ((make (i + 1) init) ++ 
                                 drop (i + 1) l)
         )). { admit. } { admit. } { admit. }
   intros i Hi.
   xdestruct.
   xvals.
   { admit. }
Admitted.
