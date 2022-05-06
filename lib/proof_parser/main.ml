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
  |> Iter.to_list

let statement_0 = List.hd asts


let () =
  match statement_0 with
  | Serapi.Serapi_protocol.CoqString _ -> print_endline "CoqString"
  |Serapi.Serapi_protocol.CoqSList _ -> print_endline "CoqSList"
                                          
  |Serapi.Serapi_protocol.CoqPp _ -> print_endline "CoqPp"
  |Serapi.Serapi_protocol.CoqLoc _ -> print_endline "CoqLoc"
                                        
  |Serapi.Serapi_protocol.CoqTok _ -> print_endline "CoqTok"
  |Serapi.Serapi_protocol.CoqDP _ -> print_endline "CoqDP"
                                       
  |Serapi.Serapi_protocol.CoqAst _ -> print_endline "CoqAst"
  |Serapi.Serapi_protocol.CoqOption (_ , _) -> print_endline "CoqOption"
  |Serapi.Serapi_protocol.CoqConstr _ -> print_endline "CoqConstr"
  |Serapi.Serapi_protocol.CoqExpr _
    -> print_endline "CoqExpr"
  |Serapi.Serapi_protocol.CoqMInd (_, _) -> print_endline "CoqMInd"
  |Serapi.Serapi_protocol.CoqEnv _
    -> print_endline "CoqEnv"
  |Serapi.Serapi_protocol.CoqTactic (_, _) -> print_endline "CoqTactic"
  |Serapi.Serapi_protocol.CoqLtac _
    -> print_endline "CoqLtac"
  |Serapi.Serapi_protocol.CoqGenArg _ -> print_endline "CoqGenArg"
  |Serapi.Serapi_protocol.CoqQualId _
    -> print_endline "CoqQualId"
  |Serapi.Serapi_protocol.CoqGlobRef _ -> print_endline "CoqGlobRef"
  |Serapi.Serapi_protocol.CoqGlobRefExt _
    -> print_endline "CoqGlobRefExt"
  |Serapi.Serapi_protocol.CoqImplicit _ -> print_endline "CoqImplicit"
  |Serapi.Serapi_protocol.CoqProfData _
    -> print_endline "CoqProfData"
  |Serapi.Serapi_protocol.CoqNotation _ -> print_endline "CoqNotation"
  |Serapi.Serapi_protocol.CoqUnparsing
     (_, _, _) -> print_endline "CoqUnparsing"
  |Serapi.Serapi_protocol.CoqGoal _
    -> print_endline "CoqGoal"
  |Serapi.Serapi_protocol.CoqExtGoal _ -> print_endline "CoqExtGoal"
  |Serapi.Serapi_protocol.CoqProof 
     (_, _) -> print_endline "CoqProof"
  |Serapi.Serapi_protocol.CoqAssumptions _
    -> print_endline "CoqAssumptions"
  |Serapi.Serapi_protocol.CoqComments _ -> print_endline "CoqComments"
