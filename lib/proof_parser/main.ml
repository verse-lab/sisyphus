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
| Serapi.Serapi_protocol.CoqString _ |Serapi.Serapi_protocol.CoqSList _
|Serapi.Serapi_protocol.CoqPp _ |Serapi.Serapi_protocol.CoqLoc _
|Serapi.Serapi_protocol.CoqTok _ |Serapi.Serapi_protocol.CoqDP _
|Serapi.Serapi_protocol.CoqAst _ |Serapi.Serapi_protocol.CoqOption (_, _)
|Serapi.Serapi_protocol.CoqConstr _ |Serapi.Serapi_protocol.CoqExpr _
|Serapi.Serapi_protocol.CoqMInd (_, _) |Serapi.Serapi_protocol.CoqEnv _
|Serapi.Serapi_protocol.CoqTactic (_, _) |Serapi.Serapi_protocol.CoqLtac _
|Serapi.Serapi_protocol.CoqGenArg _ |Serapi.Serapi_protocol.CoqQualId _
|Serapi.Serapi_protocol.CoqGlobRef _ |Serapi.Serapi_protocol.CoqGlobRefExt _
|Serapi.Serapi_protocol.CoqImplicit _ |Serapi.Serapi_protocol.CoqProfData _
|Serapi.Serapi_protocol.CoqNotation _ |Serapi.Serapi_protocol.CoqUnparsing
(_, _, _) |Serapi.Serapi_protocol.CoqGoal _
|Serapi.Serapi_protocol.CoqExtGoal _ |Serapi.Serapi_protocol.CoqProof 
(_, _) |Serapi.Serapi_protocol.CoqAssumptions _
|Serapi.Serapi_protocol.CoqComments _ -> print_endline "hello world"
