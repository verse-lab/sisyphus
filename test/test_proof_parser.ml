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
  [(Proof.Ident "A"); (Proof.Implicit ("EA", ["Enc"; "A"]));
    (Proof.Explicit ("l", ["list"; "A"])); (Proof.Explicit ("s", ["func"]))];
  spec = ("to_array", ["s"]);
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
                  formal_params = [(Proof.Ident "A"); (Proof.Implicit ("EA", ["Enc"; "A"]));
                                   (Proof.Explicit ("l", ["list"; "A"])); (Proof.Explicit ("s", ["func"]))];
                  spec = ("to_array", ["s"]);
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
  [(Proof.Ident "A"); (Proof.Implicit ("EA", ["Enc"; "A"]));
    (Proof.Explicit ("l", ["list"; "A"])); (Proof.Explicit ("s", ["func"]))];
  spec = ("to_array", ["s"]);
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
  [(Proof.Ident "A"); (Proof.Implicit ("EA", ["Enc"; "A"]));
    (Proof.Explicit ("l", ["list"; "A"])); (Proof.Explicit ("s", ["func"]))];
  spec = ("to_array", ["s"]);
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

let () = T.run ()
