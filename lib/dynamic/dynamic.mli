module Runtime = Runtime

module Matcher = Matcher

module Tracer = Tracer

module CompilationContext = Tracer.CompilationContext

module Concrete = Concrete

type scoring_function = Matcher.sanitized_state -> Matcher.sanitized_state -> float option
(** [scoring_function] ranks the similarity of two dynamic execution states. *)


val build_alignment:
  ?compilation_env:CompilationContext.t ->
  ?scorers:scoring_function list ->
  deps:string list -> old_program:Lang.Expr.t Lang.Program.t -> new_program:Lang.Expr.t Lang.Program.t -> unit -> Matcher.t
(** [build_alignment ?compilation_env ?scorers ~deps ~old_program
   ~new_program] returns a function [unit -> Matcher.t] that
   constructs a program alignment between [old_program] and
   [new_program] using dynamic tracing. *)

val build_concrete_trace:
  ?compilation_env:CompilationContext.t -> deps:string list -> Lang.Expr.t Lang.Program.t -> unit -> Concrete.t
(** [build_concrete_trace ?compilation_env ~deps prog] returns a
   function [unit -> Concrete.t] that constructs a concrete execution
   trace for program [prog]. *)
