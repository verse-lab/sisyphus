[@@@warning "-23"]
open Containers
module StringMap = Map.Make(String)

type t = {
  lambda: (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t;
  (** mapping of proof vars encoding lambdas to their corresponding definitions and observation points. *)
  bindings: string StringMap.t;
  (** mapping of proof vars (i.e [idx]) to their corresponding program variables.  *)
}

let initial_env = {lambda=StringMap.empty; bindings=StringMap.empty}

let has_definition env v = StringMap.mem v env.lambda

let is_pure_lambda env v =
  StringMap.find_opt v env.lambda
  |> Option.exists (fun (_, body) -> Program_utils.is_pure body)

let add_proof_binding env ~proof_var ~program_var =
  {env with bindings=StringMap.add proof_var program_var env.bindings}

let add_lambda_def (t: Proof_context.t) env name body =
  {env with lambda=StringMap.add name (t.current_program_id, body) env.lambda}

let find_pure_lambda_def env name =
  StringMap.find_opt name env.lambda
  |> Option.flat_map (Option.if_ (fun (_, body) -> Program_utils.is_pure body))

let env_to_defmap env =
  StringMap.map snd env.lambda
