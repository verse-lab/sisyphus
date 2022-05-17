open Containers

(**
   @param dir directory in which to execute coq queries
   @param proof_str string representation of proof script
   @param should_exec whether the script should be executed by Coq before parsing
*)
let send_to_coq dir proof_str should_exec =
  let module Ctx =
    Coq.Proof.Make(struct
      let verbose = false
      let libs = [
        Coq.Coqlib.make
          ~path:(Fpath.of_string dir |> Result.get_exn)
          "Proofs"
      ]
    end) in

  Ctx.add proof_str;
  if should_exec then Ctx.exec();

  let start = Ctx.size() - 1 in

  let query start  =
    Iter.int_range_by ~step:(-1) start 0
    |> Iter.filter_map (fun at -> Ctx.query ~at Serapi.Serapi_protocol.Ast)
    |> Iter.flat_map_l Fun.id in

  query start |> Iter.to_list

let to_vernac = let open Serapi.Serapi_protocol in function [@warning "-8"]
    | CoqAst {v = {control; attrs; expr}; _} -> Some expr
    | _ -> None

