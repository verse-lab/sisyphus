open Containers
module Embedding = Proof_term_embedding
module StringMap : module type of Map.Make(String)

type lambda_env = (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t
type obs = Dynamic.Concrete.context * Dynamic.Concrete.heap_context
type invariant_spec = string * string list
type invariant = Lang.Expr.t * Lang.Expr.t list
type 'a tester = 'a -> bool

(** [analyze env obs invariant_spec term ctx] when given an
   environment [env], a concrete observation [obs], an invariant
   specification [invariant_spec], a proof term [term] and a
   compilation context [ctx], returns an executable test that when
   given a candidate invariant [inv] will return a boolean indicating
   whether the invariant dynamically holds during the execution of the
   function or not. *)
val analyse : lambda_env -> obs -> invariant_spec -> Constr.t ->
    Dynamic.CompilationContext.t -> invariant tester
