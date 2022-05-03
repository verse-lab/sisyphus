module CompilationContext : sig

  type t

  val init : unit -> t

  val compile : t -> string -> unit

  val eval : t -> Parsetree.expression -> 'a

end

type program = string list * Lang.Expr.t Lang.Program.t

val compile:
  CompilationContext.t -> deps:string list -> prog:Lang.Expr.t Lang.Program.t -> Longident.t

val generate_trace:
  CompilationContext.t -> Longident.t -> Parsetree.expression list -> Sisyphus_tracing.trace

val bitrace: CompilationContext.t -> program -> program ->
  unit -> Sisyphus_tracing.trace * Sisyphus_tracing.trace
