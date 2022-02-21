[@@@warning "-33"]
open Containers


let () =
  print_endline @@
  Proof_parser.Proof.show (Proof_parser.Parser.parse_str {|
Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpull; [intros HLseq; apply LSeq_if in HLseq].
  case_eq l; [intros Hl|intros x xs Hl]; rewrite Hl in *.
  - xapp.
    xmatch.
    xapp.
    { intros *; xsimpl. }
  - xapp; (intros result [nxt_r [-> Hnxt_r]]).
    xmatch.
    xapp length_spec. { apply LSeq_intro; auto. applys HLseq. }
    xapp; [try math|]; [intros arr data Hdata].
    xlet.
    xseq.
    xapp (@iteri_spec _ _ f0__ s l (fun ls => arr ~> Array (ls ++ (make (length l - length ls) x)) )). {
      intros y t ys i IHl IHi.
      xapp Spec_f0__.
      xapp.
      rewrite IHl; rewrite IHi.
      apply int_index_prove; try math.
      rewrite <- length_eq. rewrite !length_app. rewrite length_cons. rewrite length_make; try math.
      xsimpl.
      rewrite length_last. math_rewrite ((length l - (1 + length t)) = ((length l - length t) - 1)).
      rewrite (@update_app_r _  _ 0 _ _ _ y IHi); try math.
      rewrite app_last_l.
      apply f_equal.
      rewrite make_eq_cons_make_pred; try (rewrite IHl; rewrite length_app; rewrite length_cons; math).
      rewrite update_zero.
      auto.
    }
    { apply LSeq_intro; rewrite Hl; eapply HLseq. }
    { rew_list; math_rewrite ((length l - 0) = length l); rewrite Hl; auto. }
    xvals. { math_rewrite ((length l - length l) = 0); rewrite make_zero; rew_list; auto. }
Qed.
|})

