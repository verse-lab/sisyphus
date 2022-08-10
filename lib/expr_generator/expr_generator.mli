module Types = Types

type ctx [@@deriving show]
(** [ctx] represents a particular expression generation context,
   capturing the variables, functions and constants that the
   enumerative synthesis will use to generate terms. *)

val ctx_pats : ctx -> Types.pat list Types.TypeMap.t

val make_raw_ctx :
  consts: (Lang.Type.t * Lang.Expr.t list) list ->
  pats: (Lang.Type.t * Types.pat list) list ->
  funcs: (Lang.Type.t * (string * Lang.Type.t list) list) list ->
  ctx


type env = string -> ((Lang.Type.t list) * Lang.Type.t) option
(** [env] represents a mapping of function names to their argument
   types and return types.  *)

val build_context: ?vars:(string * Lang.Type.t) list -> ?ints:int list -> ?funcs:string list ->
  from_id:int -> to_id:int -> env:env -> Proof_spec.Script.step list -> ctx
(** [build_context ?vars ?ints ?funcs ~from_id ~to_id ~env proof]
   constructs an enumerative-synthesis-based expression generation
   context, primed using expressions and functions taken from the
   proof script [proof], between proof points [from_id] to [to_id] *)

val generate_expression: ?initial:bool -> ?fuel:int -> ctx -> env -> Lang.Type.t -> Lang.Expr.t list
(** [generate_expression ?initial ?fuel ctx env ctx env ty] generates
   a list of candidate expressions of type [ty] using the generation
   context [ctx] and function typing environment [env] *)
