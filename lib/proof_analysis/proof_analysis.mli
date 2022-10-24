open Containers
module Embedding = Proof_term_embedding
module StringMap : module type of Map.Make(String)

type lambda_env = (Lang.Id.t * [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) StringMap.t
type hof_env = (string * Parsetree.expression) list
type obs = Dynamic.Concrete.context * Dynamic.Concrete.heap_context
type heap_spec = Proof_spec.Heap.Heaplet.t list
type invariant_spec = string * string list
type invariant = Lang.Expr.t * (string * Lang.Expr.t) list
type 'a tester = 'a -> bool

(** [analyze env lambda_env hof_env obs invariant_spec term ctx] when
   given an environment [env], a user lambda env [lambda_env], a pure
   higher order env [hof_env], a concrete observation [obs], an
   invariant specification [invariant_spec], a proof term [term] and a
   compilation context [ctx], returns an executable test that when
   given a candidate invariant [inv] will return a boolean indicating
   whether the invariant dynamically holds during the execution of the
   function or not. *)
val analyse : Environ.env -> lambda_env -> hof_env -> obs -> heap_spec -> invariant_spec -> Constr.t ->
    Dynamic.CompilationContext.t -> invariant tester
