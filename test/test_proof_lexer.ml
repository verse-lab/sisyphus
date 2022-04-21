[@@@warning "-27-26"]
open Containers

module T = Testing_utils.Make (struct let name = "proof_lexer" end);;

let collect_tokens_until_eof fn =
  let rec loop acc =
    match fn () with
    | Proof_parser.Raw_parser.EOF as tok -> List.rev (tok :: acc)
    | tok -> loop (tok :: acc) in
  loop []

let token_list = Alcotest.testable (List.pp Proof_parser.Raw_parser.pp_token) (List.equal Proof_parser.Raw_parser.equal_token)

let check_produces_tokens str tokens () =
  let lexed_tokens =
    let lexbuf = Sedlexing.Utf8.from_string str in
    let token () = Proof_parser.Lexer.token lexbuf in
    collect_tokens_until_eof token in
  Alcotest.check token_list "lexed to the expected sequence of tokens"
    tokens lexed_tokens;;

let check_can_be_lexed str count () =
  let lexed_tokens =
    let lexbuf = Sedlexing.Utf8.from_string str in
    let token () = Proof_parser.Lexer.token lexbuf in
    collect_tokens_until_eof token in
  Alcotest.(check int) "lexes without exception" count (List.length lexed_tokens);;

T.add_test "lexes prelude" @@
check_produces_tokens
  {|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old.

|}
  Proof_parser.(Raw_parser.[
    DIRECTIVE (Command.SetFlag "Implicit Arguments");
    FULL_STOP;
    DIRECTIVE (Command.ImportFrom ("CFML", ["WPLib"; "Stdlib"]));
    FULL_STOP;
    DIRECTIVE (Command.ImportFrom ("TLC", ["LibListZ"]));
    FULL_STOP;
    DIRECTIVE (Command.ImportFrom ("Proofs", ["Verify_seq_to_array_utils"]));
    FULL_STOP;
    DIRECTIVE (Command.ImportFrom ("Proofs", ["Seq_to_array_old"]));
    FULL_STOP;
    EOF
  ]);;

T.add_test "lexes theorem" @@
check_produces_tokens
  {|
Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
|}
  Proof_parser.(Raw_parser.[
    LEMMA; IDENT "to_array_spec"; COLON; FORALL;
        IDENT "A";
        IMPLICIT_LBRACE; IDENT "EA"; COLON; IDENT "Enc"; IDENT "A"; IMPLICIT_RBRACE;
        LPAREN; IDENT "l"; COLON; IDENT "list"; IDENT "A"; RPAREN;
        LPAREN; IDENT "s"; COLON; IDENT "func"; RPAREN;
    COMMA;
    SPEC; LPAREN; IDENT "to_array" ; IDENT "s"; RPAREN;
    PRE; LPAREN; PURE_LBRACE; IDENT "LSeq"; IDENT "l"; IDENT "s"; RSQBRACE; RPAREN;
    POST; LPAREN; FUN; IDENT "a"; ARROW; IDENT "a"; PTS; IDENT "Array"; IDENT "l"; RPAREN;
    FULL_STOP;
    EOF
  ]);;

T.add_test "lexes longer sequences of proof script with cases" @@
check_produces_tokens {|
  xcf.
  xpullpure HLseq.
  - xapp.
    xmatch_case_0.
    xapp.
    { intros *; xsimpl. }
  - xapp; (intros result [nxt_r [-> Hnxt_r]]).
    xmatch_case_1.
    xapp length_spec. { apply LSeq_intro; auto. applys HLseq. }
    xapp; [try math|]; [intros arr data Hdata].
|} [
  XCF; FULL_STOP;
  XPULLPURE; IDENT "HLseq"; FULL_STOP;
  PROOF_DASH_OR_SUB; XAPP; FULL_STOP;
        XMATCH_CASE_N 0; FULL_STOP;
        XAPP; FULL_STOP; COQ_PROOF "{ intros *; xsimpl. }";
  PROOF_DASH_OR_SUB; XAPP; SEMI_WITH_COQ_PROOF "(intros result [nxt_r [-> Hnxt_r]])"; FULL_STOP;
              XMATCH_CASE_N 1; FULL_STOP;
              XAPP; IDENT "length_spec"; FULL_STOP; COQ_PROOF "{ apply LSeq_intro; auto. applys HLseq. }";
              XAPP; SEMI_WITH_COQ_PROOF "[try math|]"; SEMI_WITH_COQ_PROOF "[intros arr data Hdata]"; FULL_STOP;
  EOF
];;

T.add_test "full proof script can be lexed" @@
check_can_be_lexed {|
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
|} 135




let () = T.run ()
