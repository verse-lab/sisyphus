open Containers

let () =
  print_endline "initial: hello world";
  let module Ctx =
    Proof_validator.Proof.Make(struct
      let verbose = false
      let libs = [
        Proof_validator.Coqlib.make
          ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array" |> Result.get_exn)
          "Proofs"
      ]
    end) in

  (*   Ctx.add "Set Implicit Arguments.
   * 
   * From CFML Require Import WPLib Stdlib.
   * From TLC Require Import LibListZ.
   * 
   * From Proofs Require Import Verify_seq_to_array_utils.
   * From Proofs Require Import Seq_to_array_old_ml.
   * ";
   *   Ctx.add "Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
   *   SPEC (to_array s)
   *     PRE (\\[LSeq l s])
   *     POST (fun a => a ~> Array l).
   * Proof using.
   *   xcf.
   *   xpullpure HLseq.
   *   apply LSeq_if in HLseq as Hs.
   *   assert (1 = 1). { 
   * ";
   *   Ctx.exec ();
   *   print_endline (Ctx.debug_current_goal ());
   *   print_endline "final: hello world" *)

  let text = 
    "Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old_ml.

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpullpure HLseq.
  apply LSeq_if in HLseq as Hs.
  xapp Hs.
  intros nxt Hnxt.
  case nxt as [ | x nxt2] eqn: H.
  - xmatch_case_0.
    xvalemptyarr. { admit. }
  - xmatch.
    xapp (length_spec s l); auto.
    (* unification point 1 *)
    xalloc arr data Hdata.
    xletopaque f Hf.
    xseq.
    xapp (iteri_spec f s l
                     (fun ls => arr ~> Array (ls ++ (make (length l - length ls) x)) )
         )    . { admit. } { admit. } { admit. } 
    (* unification point 2 *)
    xvals. { admit. }
Admitted.
" in
  Ctx.add text;
  Ctx.exec ();
  let proof_length = ref (Ctx.size () - 1) in
  while !proof_length > 0 do
    begin match Ctx.query ~at:!proof_length Serapi.Serapi_protocol.Ast with
    | None -> print_endline "could not parse program :<"
    | Some ast ->
      List.iter (fun ast ->
        print_endline @@
        Format.sprintf "%a" Pp.pp_with (Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty ast)
      ) ast
    end;

    decr proof_length
  done;

