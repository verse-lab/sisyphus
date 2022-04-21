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

let to_array_spec = Proof_parser.(Proof.Spec (
      [
        (Explicit ("A", Type [ "Type" ]));
        (Implicit ("EA", Type ["Enc"; "A"]));
        (Explicit ("l", Type ["list"; "A"]));
        (Explicit ("s", Type ["func"]))],
      ("to_array", [Var "s"]),
      [(Pure (Predicate ("LSeq", [(Var "l"); (Var "s")]))) ],
      (Explicit ("a", Type ["array"; "A"])),
      [(Spatial (PointsTo ("a", (Predicate ("Array", [(Var "l")]))))) ]
    ))
;;

T.add_test "parses empty proof" @@
check_produces_tree
  {|
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old.

Lemma to_array_spec : forall (A: Type) `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun (a: array A) => a ~> Array l).
Proof using.
Qed.
|}
  Proof_parser.({
    Proof.directives =
      [(Command.SetFlag "Implicit Arguments");
       (Command.ImportFrom ("CFML", ["WPLib"; "Stdlib"]));
       (Command.ImportFrom ("TLC", ["LibListZ"]));
       (Command.ImportFrom ("Proofs", ["Verify_seq_to_array_utils"]));
       (Command.ImportFrom ("Proofs", ["Seq_to_array_old"]))];
    name = "to_array_spec";
    spec = to_array_spec;
    proof = []
  });;


let () = T.run ()
