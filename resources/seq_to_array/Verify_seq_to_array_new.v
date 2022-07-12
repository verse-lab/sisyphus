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
    About list_fold_spec.
    evar (sym_1: A).
    evar (sym_2: A).
    evar (sym_3: A).
    evar (I: list A -> credits -> hprop).
    evar (HI: (forall (acc : credits) (v : A) (t r : list A),
        sym_1 :: sym_2 :: sym_3 :: nil = t ++ v :: r ->
        SPEC (ftmp acc v)
        PRE ?I t acc
        POST (fun acc0 : credits => ?I (t & v) acc0))).
    pose (list_fold_spec ftmp 3 (cons sym_1 (cons sym_2 (cons sym_3 nil))) ?I ?HI).
    Print make.
    Print LibList.make.
    Eval vm_compute in (drop 1 (cons sym_1 (cons sym_2 (cons sym_3 nil)))).
  Set Printing All.
  About CFML.Stdlib.List_ml.fold_left_cf__.
Print Wpgen_body.
    Check make.
    Print Z. int.
    Set Printing .
    Check 10.

    Eval compute in (make 10 0).
    Print make.
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
