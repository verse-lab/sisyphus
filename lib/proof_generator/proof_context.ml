open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type coq_ctx = (module Coq.Proof.PROOF)

type t = {
  ctx: coq_ctx;
  mutable current_program_id: Lang.Id.t;
  alignment: Dynamic.Matcher.t;
}

let next_program_id t =
  t.current_program_id <- Lang.Id.incr t.current_program_id

let append {ctx; _} =
  let module Ctx = (val ctx) in
  Format.ksprintf ~f:(fun res ->
    Ctx.add res;
    Ctx.exec ()
  )

let extract_proof_script {ctx; _} =
  let module Ctx = (val ctx) in
  let proof_length = Ctx.size () in
  let buf = Buffer.create 100 in
  for at = proof_length - 1 downto 0 do
    let ast =
      match Ctx.query ~at Serapi.Serapi_protocol.Ast with
      | Some [Serapi.Serapi_protocol.CoqAst ast] -> ast
      | _ -> failwith "unexpected response from Serapi" in
    let ast_str =
      Proof_debug.coqobj_to_string (Serapi.Serapi_protocol.CoqAst ast) in
    Buffer.add_string buf ast_str;
    Buffer.add_string buf "\n";
  done;
  Buffer.contents buf

let subproofs {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some goals -> goals
  | None -> failwith "unable to retrieve subproofs - serapi returned None."

let current_subproof {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some (goal :: _) -> goal
  | Some [] -> failwith "failed to obtain subproof - serapi returned no remaining subproofs."
  | None -> failwith "unable to retrieve subproof - serapi returned None."

let current_goal t =
  match (current_subproof t).goals with
  | [goal] -> goal
  | [] -> failwith "failed to obtain focused goal - serapi returned no focused goals."
  | _ -> failwith "failed to obtain focused goal - serapi returned multiple focused goals"

let env {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Env
  |> Option.flat_map (fun env ->
    match env with
    |[Serapi.Serapi_protocol.CoqEnv env] -> Some env
    | _ -> None
  )
  |> function
  | Some v -> v
  | None -> failwith "unable to obtain proof env - serapi returned None."

let typeof {ctx; _} txt =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.(TypeOf txt)
  |> Option.flat_map Serapi.Serapi_protocol.(function
    |[CoqConstr constr] -> Some constr
    | _ -> None    
  )

let definition_of {ctx; _} txt =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.(TypeOf txt)
  |> Option.flat_map Serapi.Serapi_protocol.(function
    |[CoqMInd (name, def)] -> Some def
    | _ -> None    
  )

let search t query =
  let env = env t in
  let evd = Evd.from_env env in
  let acc = ref [] in
  Search.search env evd query ([], false) (fun refr kind _ typ ->
    acc := (refr,kind,typ) :: !acc
  );
  !acc

let pretty_print_current_goal t =
  let env = env t in
  print_endline @@ "current goal: \n" ^
                   Format.sprintf "%a" Pp.pp_with
                     (Serapi.Serapi_protocol.gen_pp_obj
                        env Evd.empty (Serapi.Serapi_protocol.CoqGoal (current_subproof t)))
let debug_print_current_goal t =
  print_endline @@ "current goal: \n" ^ Proof_debug.constr_to_string (current_goal t).ty

let current_names t =
  let goal = current_goal t in
  goal.hyp
  |> List.to_iter
  |> Iter.filter_map (fun (name, _, _) -> List.last_opt name)
  |> Iter.map Names.Id.to_string
  |> StringSet.of_iter

let fresh ?(base="tmp") t =
  let names = current_names t in
  let name_in_use name =
    StringSet.mem name names in
  let rec loop incr =
    let name = Format.sprintf "%s%d" base incr in 
    if name_in_use name
    then loop (incr + 1)
    else name in
  if name_in_use base
  then loop 0
  else base

let init ~prelude ~spec ~alignment ~ctx =
  let module Ctx = (val ctx : Coq.Proof.PROOF) in
  Ctx.reset ();
  Ctx.add prelude;
  Ctx.add spec;
  Ctx.exec ();
  {
    ctx;
    alignment;
    current_program_id=Lang.Id.init
  }
