open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Debug utils for working with Coq" "prf.utils.dbg"))

let coqobj_to_string v =
  Format.to_string Pp.pp_with @@
  Serapi.Serapi_protocol.gen_pp_obj Environ.empty_env Evd.empty v

let tag ty =
  match Constr.kind ty with
  | Constr.Rel _ -> "Rel"
  | Constr.Var _ -> "Var"
  | Constr.Meta _ -> "Meta"
  | Constr.Evar _ -> "Evar"
  | Constr.Sort _ -> "Sort"
  | Constr.Cast (_, _, _) -> "Cast"
  | Constr.Prod (_, _, _) -> "Prod"
  | Constr.Lambda (_, _, _) -> "Lambda"
  | Constr.LetIn (_, _, _, _) -> "LetIn"
  | Constr.App (_, _) -> "App"
  | Constr.Const _ -> "Const"
  | Constr.Ind _ -> "Ind"
  | Constr.Construct _ -> "Construct"
  | Constr.Case (_, _, _, _, _, _, _) -> "Case"
  | Constr.Fix _ -> "Fix"
  | Constr.CoFix _ -> "CoFix"
  | Constr.Proj (_, _) -> "Proj"
  | Constr.Int _ -> "Int"
  | Constr.Float _ -> "Float"
  | Constr.Array (_, _, _, _)  -> "Array"  

let globref_to_string : Names.GlobRef.t -> string = function
  | VarRef var -> Names.Id.to_string var
  | ConstRef c -> Names.Constant.to_string c
  | IndRef (id, _) -> Names.MutInd.to_string id
  | ConstructRef ((id, _), _) -> Names.MutInd.to_string id

let constr_to_string s = Format.sprintf "%a" Pp.pp_with (Constr.debug_print s)

let constr_to_string_pretty s =
  coqobj_to_string Serapi.Serapi_protocol.(CoqConstr s)
  
let universe_to_string u =
  Format.to_string Pp.pp_with @@
  Univ.Universe.pr u

let ast ?at (module Ctx: Coq.Proof.PROOF)  =
  Ctx.query ?at Serapi.Serapi_protocol.Ast
  |> Option.flat_map (function
    | [Serapi.Serapi_protocol.CoqAst v] -> Some v.v.expr
    | _ -> None
  ) |> Option.get_exn_or "failed to get ast"

let typeof ?at (module Ctx: Coq.Proof.PROOF) name =
  let ty =
    Ctx.query ?at Serapi.Serapi_protocol.(TypeOf name)
    |> Option.map (List.map coqobj_to_string)
    |> Option.map (String.concat "; ")
    |> Option.get_or ~default:"NONE"
    |> (fun s -> "[" ^ s ^ "]") in
  Log.debug (fun f -> f "%s" ty)

