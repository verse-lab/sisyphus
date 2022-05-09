module Runtime = Runtime

module Matcher = Matcher

module Tracer = Tracer

module CompilationContext = Tracer.CompilationContext

type scoring_function = Matcher.sanitized_state -> Matcher.sanitized_state -> float option
(** [scoring_function] ranks the similarity of two dynamic execution states. *)


val build_alignment:
  ?compilation_env:CompilationContext.t ->
  ?scorers:scoring_function list ->
  deps:string list -> old_program:string -> new_program:string -> unit -> Matcher.t
(** [build_alignment ?compilation_env ?scorers ~deps ~old_program
   ~new_program ()] constructs a program alignment between
   [old_program] and [new_program] using dynamic tracing. *)
