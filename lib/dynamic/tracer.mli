module CompilationContext : sig

  type t
  (** encodes an opaque representation of an OCaml compilation context. *)

  val init : unit -> t
  (** [init ()] returns a fresh OCaml compilation context. *)

  val compile : t -> string -> unit
  (** [compile ctx txt] compiles the OCaml source code [txt] in the compilation context [ctx]. *)

  val eval : t -> Parsetree.expression -> 'a
  (** [eval ctx expr] evaluates an expression [expr] in the compilation context [ctx].  *)

end

type program = string list * Lang.Expr.t Lang.Program.t
(** a program is represented as a tuple of [(deps, ast)] where deps
   should be a list of files that the ast depends on being compiled. *)

val compile: ?deep: bool ->
  CompilationContext.t -> deps:string list -> prog:Lang.Expr.t Lang.Program.t -> Longident.t
(** [compile ?deep ctx ~deps ~prog] compiles the program [prog] with
   tracing annotations, first loading and compiling all of its
   dependencies, and returns a unique identifier to represent the
   compiled expression. If [deep] is provided, then tracing
   annotations are also generated within any nested lambdas in
   [prog]. *)

val generate_trace:
  CompilationContext.t -> Longident.t -> Parsetree.expression list -> Sisyphus_tracing.trace
(** [generate_trace ctx fn args] evaluates [fn] on arguments [args]
   and returns the trace of events produced by calls to
   [Sisyphus_tracing.observe]. *)

val bitrace: CompilationContext.t -> program -> program ->
  unit -> Sisyphus_tracing.trace * Sisyphus_tracing.trace
(** [bitrace ctx p1 p2] returns a function [unit -> trace * trace]
   that can be called one or more times to generate fresh traces of
   programs [p1] and [p2] on the same inputs. *)

val execution_trace: CompilationContext.t -> program -> unit -> Sisyphus_tracing.trace
(** [execution_trace ctx p1] returns a function [unit -> trace] that
   can be called one or more times to generate deep execution traces
   of the program [p1]. *)
