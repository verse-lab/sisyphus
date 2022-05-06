open Containers

let proof_str = IO.with_in "../../resources/seq_to_array/Verify_seq_to_array_old.v" IO.read_all

let () = print_endline @@ "Hello world" ^ proof_str

let asts =
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string "../../_build/default/resources/seq_to_array" |> Result.get_exn)
          "Proofs"
      ] 
    end) in
  Ctx.add proof_str;
  Ctx.exec();

  let start = Ctx.size() - 1 in

  (* TODO: Candidate for function*)
  Iter.int_range_by ~step:(-1) start 0
  |> Iter.filter_map (fun at ->
   Ctx.query ~at Serapi.Serapi_protocol.Ast 
  )
  |> Iter.flat_map_l Fun.id
  |> Iter.filter_map (function Serapi.Serapi_protocol.CoqAst v ->
                      
                      Some v.v
                      | _ -> None
                      )
  |> Iter.to_list

let statement_0 = List.hd asts


let () =
  match statement_0.expr with
  | Vernacexpr.VernacLoad (_, _) |Vernacexpr.VernacReservedNotation (_, _)
|Vernacexpr.VernacOpenCloseScope (_, _) |Vernacexpr.VernacDeclareScope _
|Vernacexpr.VernacDelimiters (_, _) |Vernacexpr.VernacBindScope (_, _)
|Vernacexpr.VernacNotation (_, _, _, _) |Vernacexpr.VernacNotationAddFormat
(_, _, _) |Vernacexpr.VernacDeclareCustomEntry _ |Vernacexpr.VernacDefinition
(_, _, _) |Vernacexpr.VernacStartTheoremProof (_, _)
|Vernacexpr.VernacEndProof _ |Vernacexpr.VernacExactProof _
|Vernacexpr.VernacAssumption (_, _, _) |Vernacexpr.VernacInductive (_, _)
|Vernacexpr.VernacFixpoint (_, _) |Vernacexpr.VernacCoFixpoint (_, _)
|Vernacexpr.VernacScheme _ |Vernacexpr.VernacCombinedScheme (_, _)
|Vernacexpr.VernacUniverse _ |Vernacexpr.VernacConstraint _
|Vernacexpr.VernacBeginSection _ |Vernacexpr.VernacEndSegment _
|Vernacexpr.VernacRequire (_, _, _) |Vernacexpr.VernacImport (_, _, _)
|Vernacexpr.VernacCanonical _ |Vernacexpr.VernacCoercion (_, _, _)
|Vernacexpr.VernacIdentityCoercion (_, _, _)
|Vernacexpr.VernacNameSectionHypSet (_, _) |Vernacexpr.VernacInstance
(_, _, _, _, _) |Vernacexpr.VernacDeclareInstance (_, _, _, _)
|Vernacexpr.VernacContext _ |Vernacexpr.VernacExistingInstance _
|Vernacexpr.VernacExistingClass _ |Vernacexpr.VernacDeclareModule
(_, _, _, _) |Vernacexpr.VernacDefineModule (_, _, _, _, _)
|Vernacexpr.VernacDeclareModuleType (_, _, _, _) |Vernacexpr.VernacInclude _
|Vernacexpr.VernacAddLoadPath _ |Vernacexpr.VernacRemoveLoadPath _
|Vernacexpr.VernacAddMLPath _ |Vernacexpr.VernacDeclareMLModule _
|Vernacexpr.VernacChdir _ |Vernacexpr.VernacResetName _
|Vernacexpr.VernacResetInitial |Vernacexpr.VernacBack _
|Vernacexpr.VernacCreateHintDb (_, _) |Vernacexpr.VernacRemoveHints (_, _)
|Vernacexpr.VernacHints (_, _) |Vernacexpr.VernacSyntacticDefinition
(_, _, _) |Vernacexpr.VernacArguments (_, _, _, _) |Vernacexpr.VernacReserve
_ |Vernacexpr.VernacGeneralizable _ |Vernacexpr.VernacSetOpacity _
|Vernacexpr.VernacSetStrategy _ 
|Vernacexpr.VernacAddOption (_, _) |Vernacexpr.VernacRemoveOption (_, _)
|Vernacexpr.VernacMemOption (_, _) |Vernacexpr.VernacPrintOption _
|Vernacexpr.VernacCheckMayEval (_, _, _) |Vernacexpr.VernacGlobalCheck _
|Vernacexpr.VernacDeclareReduction (_, _) |Vernacexpr.VernacPrint _
|Vernacexpr.VernacSearch (_, _, _) |Vernacexpr.VernacLocate _
|Vernacexpr.VernacRegister (_, _) |Vernacexpr.VernacPrimitive (_, _, _)
|Vernacexpr.VernacComments _ |Vernacexpr.VernacAbort _
|Vernacexpr.VernacAbortAll |Vernacexpr.VernacRestart |Vernacexpr.VernacUndo _
|Vernacexpr.VernacUndoTo _ |Vernacexpr.VernacFocus _
|Vernacexpr.VernacUnfocus |Vernacexpr.VernacUnfocused
|Vernacexpr.VernacBullet _ |Vernacexpr.VernacSubproof _
|Vernacexpr.VernacEndSubproof |Vernacexpr.VernacShow _
|Vernacexpr.VernacCheckGuard |Vernacexpr.VernacProof (_, _)
|Vernacexpr.VernacProofMode _ |Vernacexpr.VernacExtend (_, _) -> print_endline "hello world"
|Vernacexpr.VernacSetOption (_, _, _) -> print_endline "Found set option"
