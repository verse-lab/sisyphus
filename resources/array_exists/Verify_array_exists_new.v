Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.

From Common Require Import Tactics Utils Solver Verify_opt.

From ProofsArrayExists Require Import Array_exists_new_ml.

Lemma array_exists_spec :
  forall (A : Type) `{EA : Enc A} (a : array A) (f : func) (l : list A) (fp: A -> bool),
    (forall (a: A),
        SPEC_PURE (f a)
         POST (fun b => \[b = fp a])
    ) ->
  SPEC (array_exists a f)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = List.existsb fp l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xletopaque tmp Htmp.
  xapp (until_upto_spec unit 0 (length l) tmp
          (fun (i: int) (b: option unit) =>
             \[b = opt_of_bool (List.existsb fp (take i l))] \*
               a ~> Array l)
       ). {
    sis_solve_start.
    apply opt_of_bool_some_intro; apply opt_of_bool_none in H0.
    rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
    math_rewrite ((i + 1 - 1) = i).
    rewrite list_existsb_app; simpl; rewrite H1; simpl; rewrite H0; simpl; auto. 
    apply opt_of_bool_none_intro; apply opt_of_bool_none in H0.
    rewrite (take_pos_last IA); [|apply int_index_prove; rewrite <- ?length_eq; math].
    math_rewrite ((i + 1 - 1) = i).
    rewrite list_existsb_app; simpl; rewrite H0; destruct (fp l[i]); simpl; auto;
      contradiction H1; auto.
  }
  { math. }
  { rewrite take_zero; simpl; auto. }
  intros fin i_b Hres Hexists.
  xapp (opt_is_some_spec).
  xvals*. {
    destruct fin; destruct Hres as [Hlen Himpl]; simpl in *; try destruct u.
    - apply opt_of_bool_some in Hexists.
      rewrite <- (@list_eq_take_app_drop _ i_b l) at 1; try math.
      rewrite list_existsb_app; rewrite  Hexists; simpl; auto.
    - assert (Heq: i_b = length l) by (apply Z.eqb_eq; auto).
      rewrite Heq, take_full_length in Hexists; auto.
      apply opt_of_bool_none in Hexists; subst; auto.
  }
Qed.
