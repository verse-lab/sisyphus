Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Common Require Import Verify_combinators.
From Common Require Import Tactics Solver Utils.

From ProofsArrayIsSorted Require Import Array_is_sorted_new_ml.


Lemma array_is_sorted_spec :
  forall (a : array int) (l : list int),
  SPEC (array_is_sorted a)
  PRE (a ~> Array l)
  POST (fun (b : bool) => \[b = is_sorted l] \* a ~> Array l).
Proof using (All).
  xcf.
  xapp.
  xif as cond.
  - xvals*. { sis_list_solver. }
  - xref result.
    xletopaque tmp Htmp.
    xapp (while_downto_spec (length l - 1) 0 tmp
            (fun (i: int) (b: bool) =>
               \[ b = is_sorted (drop i l) ] \*
                 result ~~> b \*
                 a ~> Array l)
         ). {
      intros i Hi; apply Htmp; clear Htmp.
      xpullpure Hexists.
      xapp. { sis_handle_int_index_prove. }
      xapp. { sis_handle_int_index_prove. }
      xif;=> Hcond.
      - xapp.
        xapp.
        xsimpl*. {
          eapply (@not_is_sorted_gen _ 1);
            rewrite ?length_drop_nonneg; rewrite ?read_drop;
            try apply int_index_prove; try math.
          math_rewrite (i - 1 + (1 - 1) = i - 1).
          math_rewrite (i - 1 + 1 = i).
          math.
        }
      - xval.
        xapp.
        xsimpl*. {
          rewrite (@drop_cons_unfold _ Inhab_int); try math.
          assert (l[i - 1] <= l[i]) by math.
          apply is_sorted_gen;
            math_rewrite (i - 1 + 1 = i);
            auto;
            try (rewrite <- Hexists; auto);
            rewrite ?length_drop_nonneg; try math;
            rewrite ?drop_drop, ?read_drop, Z.add_0_r;
            auto; math.
        }
    } { math. } {  apply is_sorted_last_elt; auto; math. }
    intros term i Hcond Heq.
    xmatch.
    xapp.
    xvals*. {
      symmetry in Heq; symmetry.
      destruct term; simpl in Hcond; destruct Hcond as [Hlen Heq0].
      - assert (Heq0last: i = 0) by (apply Z.eqb_eq; auto).
        rewrite Heq0last in Heq; rewrite drop_zero in Heq; auto.
      - rewrite <- (@list_eq_take_app_drop _ i l); try math.
        rewrite is_sorted_app_r; auto.
    }
Qed.
