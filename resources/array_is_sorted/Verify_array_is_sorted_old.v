Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators Verify_opt.

From Common Require Import Tactics.
From Common Require Import Utils.

From ProofsArrayIsSorted Require Import Array_is_sorted_old_ml.

Definition is_sorted_internal ls :=
  match ls with
  | h :: t =>
      is_some (List.fold_left
                 (fun '(acc: option (bool * int)) (v: int) =>
                    match acc with
                    | None => None
                    | Some (b, p_vl) =>
                        if v <=? p_vl 
                        then Some (true, v)
                        else None
                    end
                 ) t (Some (true, h)))
  | nil => true
  end.
Definition is_sorted ls := is_sorted_internal (rev ls).

Lemma array_is_sorted_spec :
  forall (a: array int) (l: list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[ b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_downto_spec (length l - 1) 0 tmp
          (fun (i: int) (res: option bool) =>
             a ~> Array l \*
               \[res = res]
          )
       ). { admit. } { admit. } { admit. }
  intros res i [Hi Himpl] Heq.
  xapp (opt_is_some_spec).
  xlet.
  xvals*. {
    admit.
  }
Admitted.
