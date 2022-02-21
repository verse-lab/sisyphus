[@@@warning "-27-26-33"]
open Containers

module T = Testing_utils.Make (struct let name = "proof_parser" end);;

let proof = Alcotest.testable (Proof_parser.Proof.pp) Proof_parser.Proof.equal
let pure_expression =
  Alcotest.testable
    (Proof_parser.Proof.pp_pure_expression)
    Proof_parser.Proof.equal_pure_expression
let assertion =
  Alcotest.testable
    (Proof_parser.Proof.pp_assertion)
    Proof_parser.Proof.equal_assertion


let check_produces_tree str tree () =
  Alcotest.check proof "proof is parsed correctly"
    (Proof_parser.Parser.parse_str str) tree;;

let check_parser_without_failing str () =
  let had_exn = try ignore (Proof_parser.Parser.parse_str str); false with _ -> true in
  Alcotest.(check bool) "proof is parsed without throwing an exceptions"
    false had_exn;;

T.add_test "parses empty proof" @@
check_produces_tree
  {|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old.

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
Qed.
|}
  Proof_parser.({ Proof.directives =
  [(Command.SetFlag "Implicit Arguments");
    (Command.ImportFrom ("CFML", ["WPLib"; "Stdlib"]));
    (Command.ImportFrom ("TLC", ["LibListZ"]));
    (Command.ImportFrom ("Proofs", ["Verify_seq_to_array_utils"]));
    (Command.ImportFrom ("Proofs", ["Seq_to_array_old"]))];
  name = "to_array_spec";
  formal_params =
  [(Proof.Ident "A"); (Proof.Implicit ("EA", Type ["Enc"; "A"]));
    (Proof.Explicit ("l", Type ["list"; "A"])); (Proof.Explicit ("s", Type ["func"]))];
  spec = ("to_array", [Var "s"]);
  pre = [(Proof.Pure (Proof.Predicate ("LSeq", [(Proof.Var "l"); (Proof.Var "s")]))) ];
  post =
  ((Proof.Ident "a"),
   [(Proof.Spatial (Proof.PointsTo ("a", (Proof.Predicate ("Array", [(Proof.Var "l")]))))) ]);
  proof = [] });;


T.add_test "parses straight line proof" @@
check_produces_tree
  {|
Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpull; [intros HLseq; apply LSeq_if in HLseq].
Qed.
|}
  Proof_parser.({ Proof.directives = []; name = "to_array_spec";
                  formal_params = [(Proof.Ident "A"); (Proof.Implicit ("EA", Type ["Enc"; "A"]));
                                   (Proof.Explicit ("l", Type ["list"; "A"])); (Proof.Explicit ("s", Type ["func"]))];
                  spec = ("to_array", [Var "s"]);
                  pre = [(Proof.Pure (Proof.Predicate ("LSeq", [(Proof.Var "l"); (Proof.Var "s")])))];
                  post = ((Proof.Ident "a"),
                          [(Proof.Spatial (Proof.PointsTo ("a",
                                                           (Proof.Predicate ("Array", [(Proof.Var "l")])))))]);
                  proof = [
                    Proof.Xcf;
                    (Proof.Xpull ["[intros HLseq; apply LSeq_if in HLseq]"])
                  ] });;

T.add_test "parses proof with case at end" @@
check_produces_tree
  {|
Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpull; [intros HLseq; apply LSeq_if in HLseq].
  case_eq l; [intros Hl|intros x xs Hl]; rewrite Hl in *.
  - xapp.
  - xapp; (intros result [nxt_r [-> Hnxt_r]]).
Qed.
|}
  Proof_parser.({ Proof.directives = []; name = "to_array_spec";
  formal_params =
  [(Proof.Ident "A"); (Proof.Implicit ("EA", Type ["Enc"; "A"]));
    (Proof.Explicit ("l", Type ["list"; "A"])); (Proof.Explicit ("s", Type ["func"]))];
  spec = ("to_array", [Var "s"]);
  pre =
  [(Proof.Pure (Proof.Predicate ("LSeq", [(Proof.Var "l"); (Proof.Var "s")])))
    ];
  post =
  ((Proof.Ident "a"),
   [(Proof.Spatial
       (Proof.PointsTo ("a", (Proof.Predicate ("Array", [(Proof.Var "l")])))))
     ]);
  proof =
  [Proof.Xcf; (Proof.Xpull ["[intros HLseq; apply LSeq_if in HLseq]"]);
    (Proof.CaseEq (("l", [["Hl"]; ["x"; "xs"; "Hl"]]), ["rewrite Hl in *"],
       [[(Proof.Xapp (None, [], []))];
        [(Proof.Xapp (None, ["(intros result [nxt_r [-> Hnxt_r]])"], []))]]
       ))
    ]
  });;


T.add_test "parses xapp with expression argument" @@
check_produces_tree
  {|
Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xapp (@iteri_spec _ _ f0__ s l (fun ls => arr ~> Array (ls ++ (make (length l - length ls) x)) )).
Qed.
|}
  Proof_parser.({ Proof.directives = []; name = "to_array_spec";
  formal_params =
  [(Proof.Ident "A"); (Proof.Implicit ("EA", Type ["Enc"; "A"]));
    (Proof.Explicit ("l", Type ["list"; "A"])); (Proof.Explicit ("s", Type ["func"]))];
  spec = ("to_array", [Var "s"]);
  pre =
  [(Proof.Pure (Proof.Predicate ("LSeq", [(Proof.Var "l"); (Proof.Var "s")])))
    ];
  post =
  ((Proof.Ident "a"),
   [(Proof.Spatial
       (Proof.PointsTo ("a", (Proof.Predicate ("Array", [(Proof.Var "l")])))))
     ]);
  proof =
  [Proof.Xcf;
    (Proof.Xapp (
       (Some (Proof.Predicate ("iteri_spec",
                [(Proof.Var "_"); (Proof.Var "_"); (Proof.Var "f0__");
                  (Proof.Var "s"); (Proof.Var "l");
                  (Proof.Lambda ([(Proof.Ident "ls")],
                     (Proof.HeapSpec
                        [(Proof.Spatial
                            (Proof.PointsTo ("arr",
                               (Proof.Predicate ("Array",
                                  [(Proof.Append ((Proof.Var "ls"),
                                      (Proof.Predicate ("make",
                                         [(Proof.Sub (
                                             (Proof.Predicate ("length",
                                                [(Proof.Var "l")])),
                                             (Proof.Predicate ("length",
                                                [(Proof.Var "ls")]))
                                             ));
                                           (Proof.Var "x")]
                                         ))
                                      ))
                                    ]
                                  ))
                               )))
                          ])
                     ))
                  ]
                ))),
       [], []))
    ]
  });;


T.add_test "parses full proof" @@
check_parser_without_failing
  {|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old.

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
|}
;;


T.add_test "parses updated proof as well" @@
check_parser_without_failing {|
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
|}

let () = T.run ()
