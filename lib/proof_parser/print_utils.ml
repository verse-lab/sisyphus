open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Utils for parsing proof scripts" "prf-parser.utils"))

let get_vernac_tag = function
  |Vernacexpr.VernacLoad (_, _) -> "VernacLoad"
  |Vernacexpr.VernacReservedNotation (_, _)
    -> "VernacReservedNotation"
  |Vernacexpr.VernacOpenCloseScope (_, _) -> "VernacOpenCloseScope"
  |Vernacexpr.VernacDeclareScope _
    -> "VernacDeclareScope"
  |Vernacexpr.VernacDelimiters (_, _) -> "VernacDelimiters"
  |Vernacexpr.VernacBindScope (_, _)
    -> "VernacBindScope"
  |Vernacexpr.VernacNotation (_, _, _, _) -> "VernacNotation"
  |Vernacexpr.VernacNotationAddFormat
      (_, _, _) -> "VernacNotationAddFormat"
  |Vernacexpr.VernacDeclareCustomEntry _ -> "VernacDeclareCustomEntry"
  |Vernacexpr.VernacDefinition
      (_, _, _) -> "VernacDefinition"
  |Vernacexpr.VernacStartTheoremProof (_, _)
    -> "VernacStartTheoremProof"
  |Vernacexpr.VernacEndProof _ -> "VernacEndProof"
  |Vernacexpr.VernacExactProof _
    -> "VernacExactProof"
  |Vernacexpr.VernacAssumption (_, _, _) -> "VernacAssumption"
  |Vernacexpr.VernacInductive (_, _)
    -> "VernacInductive"
  |Vernacexpr.VernacFixpoint (_, _) -> "VernacFixpoint"
  |Vernacexpr.VernacCoFixpoint (_, _)
    -> "VernacCoFixpoint"
  |Vernacexpr.VernacScheme _ -> "VernacScheme"
  |Vernacexpr.VernacCombinedScheme (_, _)
    -> "VernacCombinedScheme"
  |Vernacexpr.VernacUniverse _ -> "VernacUniverse"
  |Vernacexpr.VernacConstraint _
    -> "VernacConstraint"
  |Vernacexpr.VernacBeginSection _ -> "VernacBeginSection"
  |Vernacexpr.VernacEndSegment _
    -> "VernacEndSegment"
  |Vernacexpr.VernacRequire (_, _, _) -> "VernacRequire"
  |Vernacexpr.VernacImport (_, _, _)
    -> "VernacImport"
  |Vernacexpr.VernacCanonical _ -> "VernacCanonical"
  |Vernacexpr.VernacCoercion (_, _, _)
    -> "VernacCoercion"
  |Vernacexpr.VernacIdentityCoercion (_, _, _)
    -> "VernacIdentityCoercion"
  |Vernacexpr.VernacNameSectionHypSet (_, _) -> "VernacNameSectionHypSet"
  |Vernacexpr.VernacInstance
      (_, _, _, _, _) -> "VernacInstance"
  |Vernacexpr.VernacDeclareInstance (_, _, _, _)
    -> "VernacDeclareInstance"
  |Vernacexpr.VernacContext _ -> "VernacContext"
  |Vernacexpr.VernacExistingInstance _
    -> "VernacExistingInstance"
  |Vernacexpr.VernacExistingClass _ -> "VernacExistingClass"
  |Vernacexpr.VernacDeclareModule
      (_, _, _, _) -> "VernacDeclareModule"
  |Vernacexpr.VernacDefineModule (_, _, _, _, _)
    -> "VernacDefineModule"
  |Vernacexpr.VernacDeclareModuleType (_, _, _, _) -> "VernacDeclareModuleType"
  |Vernacexpr.VernacInclude _
    -> "VernacInclude"
  |Vernacexpr.VernacAddLoadPath _ -> "VernacAddLoadPath"
  |Vernacexpr.VernacRemoveLoadPath _
    -> "VernacRemoveLoadPath"
  |Vernacexpr.VernacAddMLPath _ -> "VernacAddMLPath"
  |Vernacexpr.VernacDeclareMLModule _
    -> "VernacDeclareMLModule"
  |Vernacexpr.VernacChdir _ -> "VernacChdir"
  |Vernacexpr.VernacResetName _
    -> "VernacResetName"
  |Vernacexpr.VernacResetInitial -> "VernacResetInitial"
  |Vernacexpr.VernacBack _
    -> "VernacBack"
  |Vernacexpr.VernacCreateHintDb (_, _) -> "VernacCreateHintDb"
  |Vernacexpr.VernacRemoveHints (_, _)
    -> "VernacRemoveHints"
  |Vernacexpr.VernacHints (_, _) -> "VernacHints"
  |Vernacexpr.VernacSyntacticDefinition
      (_, _, _) -> "VernacSyntacticDefinition"
  |Vernacexpr.VernacArguments (_, _, _, _) -> "VernacArguments"
  |Vernacexpr.VernacReserve
      _ -> "VernacReserve"
  |Vernacexpr.VernacGeneralizable _ -> "VernacGeneralizable"
  |Vernacexpr.VernacSetOpacity _
    -> "VernacSetOpacity"
  |Vernacexpr.VernacSetStrategy _
    -> "VernacSetStrategy"
  |Vernacexpr.VernacAddOption (_, _) -> "VernacAddOption"
  |Vernacexpr.VernacRemoveOption (_, _)
    -> "VernacRemoveOption"
  |Vernacexpr.VernacMemOption (_, _) -> "VernacMemOption"
  |Vernacexpr.VernacPrintOption _
    -> "VernacPrintOption"
  |Vernacexpr.VernacCheckMayEval (_, _, _) -> "VernacCheckMayEval"
  |Vernacexpr.VernacGlobalCheck _
    -> "VernacGlobalCheck"
  |Vernacexpr.VernacDeclareReduction (_, _) -> "VernacDeclareReduction"
  |Vernacexpr.VernacPrint _
    -> "VernacPrint"
  |Vernacexpr.VernacSearch (_, _, _) -> "VernacSearch"
  |Vernacexpr.VernacLocate _
    -> "VernacLocate"
  |Vernacexpr.VernacRegister (_, _) -> "VernacRegister"
  |Vernacexpr.VernacPrimitive (_, _, _)
    -> "VernacPrimitive"
  |Vernacexpr.VernacComments _ -> "VernacComments"
  |Vernacexpr.VernacAbort _
    -> "VernacAbort"
  |Vernacexpr.VernacAbortAll -> "VernacAbortAll"
  |Vernacexpr.VernacRestart -> "VernacRestart"
  |Vernacexpr.VernacUndo _
    -> "VernacUndo"
  |Vernacexpr.VernacUndoTo _ -> "VernacUndoTo"
  |Vernacexpr.VernacFocus _
    -> "VernacFocus"
  |Vernacexpr.VernacUnfocus -> "VernacUnfocus"
  |Vernacexpr.VernacUnfocused
    -> "VernacUnfocused"
  |Vernacexpr.VernacBullet _ -> "VernacBullet"
  |Vernacexpr.VernacSubproof _
    -> "VernacSubproof"
  |Vernacexpr.VernacEndSubproof -> "VernacEndSubproof"
  |Vernacexpr.VernacShow _
    -> "VernacShow"
  |Vernacexpr.VernacCheckGuard -> "VernacCheckGuard"
  |Vernacexpr.VernacProof (_, _)
    -> "VernacProof"
  |Vernacexpr.VernacProofMode _ -> "VernacProofMode"
  |Vernacexpr.VernacExtend (extend_name, args) ->
    "VernacExtend"
  |Vernacexpr.VernacSetOption (_, _, _) -> "VernacSetOption"


let string_of_coq_obj obj =
  let pp =  Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty obj in
  Format.sprintf "%a" Pp.pp_with pp

let pp_coq_obj obj =
  begin match obj with
  | Serapi.Serapi_protocol.CoqAst v ->
    Log.debug (fun f -> f "%s" (get_vernac_tag v.v.expr))
  | _ -> ()
  end;
  Log.debug (fun f -> f "%s" (string_of_coq_obj obj))

let pp_coq_objs objs =
  List.iter pp_coq_obj objs

let string_of_vexp vexp =
  Format.sprintf "%a" Pp.pp_with (Ppvernac.pr_vernac_expr vexp)
