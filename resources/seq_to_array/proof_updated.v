Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils_new.
From Proofs Require Import Seq_to_array_new.

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xlet (fun (f: func) =>
     forall (i: int) (acc: list A) (x: A),
       SPEC_PURE (f (i,acc) x)
                 POST \[= (i + 1, x :: acc)]); auto.
  { xgo*. }
  xpull; [intros HLseq; apply LSeq_if in HLseq].
  xapp (@fold_spec _ _ _ _ l f0__ (0, nil) s
                   (fun (pair: int * list A) (x: A) =>
                      let (i, acc) := pair in
                      (i + 1, x :: acc))); auto.
  { intros [i acc] x. xapp. xsimpl. auto. }
  { apply LSeq_intro; auto. }
  xmatch; [rewrite list_fold_length_rev in H0; inversion H0 as [Hlen]].
  case_eq l; [intros Hl | intros x xs Hl]; rewrite Hl in *.
  - xmatch.
    xapp; [intros x].
    xsimpl.
  - xmatch. { apply nil_eq_rev_inv in H2. inversion H2. }
    xapp; [math| intros arr data Hdata].
    xlet.
    xlet.
    xapp (@list_fold_spec A EA int _ f1__ idx rest (fun t i =>
        \[i = length l - length t - 2] \*
        arr ~> Array ((make (i + 1) init) ++ 
                                 drop (i + 1) l)
         )). {
        introv Hrst. apply Spec_f1__; clear Spec_f1__.
        assert (length (init :: rest) = length l) as Htmp by
                (rewrite H2; rewrite length_rev; rewrite Hl; auto).
        rewrite length_cons in Htmp.
        rewrite Hrst in Htmp; rewrite length_app in Htmp.
        rewrite length_cons in Htmp.
        xpull ;=> Hacc.
        xseq.
        xapp. {
          apply int_index_prove; try math.
          rewrite Hacc.
            rewrite <- length_eq.  rewrite length_app.
            rewrite length_make; try math.
        }
        xvals.
        {
          rewrite Hacc. rewrite <- Htmp.
          rewrite length_last. math.
        }
        rewrite update_app_l; try (rewrite length_make; math).        
        rewrite make_succ_r; try math.
        rewrite (@update_middle _ acc (make acc init) nil v init);
          try (rewrite length_make; math).
        rewrite app_nil_r.
        math_rewrite ((acc - 1 + 1) = acc).
        rewrite app_last_l.
        cut (v :: drop (acc + 1) l = drop acc l). {
          intros ->; auto.
        }
        rewrite Hl.
        rewrite Hrst in H2.
        rewrite <- app_cons_l in H2.
        symmetry in  H2.
        pose proof (case_rev_split (x :: xs) v (init :: t) r H2) as H1.
        rewrite H1.
        assert (length (rev r) = acc) as Hr by (rewrite length_rev; math).
        assert (length (rev r & v) = acc + 1) as Hrev by
          (rewrite length_last; rewrite length_rev; math).
        rewrite  app_cons_r at 1; rewrite <- Hrev at 1.
        rewrite <- Hr at 1.
        rewrite !drop_app_length.
        auto.
      }
   { rewrite Pidx. rewrite Hl. rewrite length_cons. rewrite length_nil. math. }
   { rewrite Hl; rewrite Pidx; rewrite !length_cons.
     math_rewrite ((1 + length xs - 2 + 1) = length xs).
     assert (length xs = length (x :: xs) - 1) as H' by (rewrite length_cons; math).
     rewrite H' at 2. symmetry in H2. rewrite (drop_last (x :: xs) H2).
     rewrite <- make_succ_r; try math.
     rewrite Hdata. rewrite length_cons.
     math_rewrite (1 + length xs = length xs + 1); auto. }
   intros i Hi.
    xmatch.
    xvals.
    {
      rewrite Hi.
      assert (length (init :: rest) = length l) as Htmp by
          (rewrite H2; rewrite length_rev; rewrite Hl; auto).
      rewrite length_cons in Htmp.
      assert (length rest = length l - 1) as Hrest by math.
      clear Htmp. rewrite Hrest.
      math_rewrite
        ((length l - (length l - 1) - 2 + 1) = 0).
      rewrite make_zero; rewrite drop_zero.
      rewrite app_nil_l.
      auto.
    }
Qed.
