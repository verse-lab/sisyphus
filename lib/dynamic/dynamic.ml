open Containers

module Tracer = Tracer

module Runtime = Runtime

module Matcher = Matcher

module CompilationContext = Tracer.CompilationContext

type scoring_function = Matcher.sanitized_state -> Matcher.sanitized_state -> float option

let build_alignment ?compilation_env ?scorers ~deps ~old_program ~new_program () =
  let compilation_env =
    match compilation_env with
    | Some env -> env
    | None -> Tracer.CompilationContext.init () in
  let old_trace, new_trace =
    Tracer.bitrace compilation_env
      (deps, old_program) (deps, new_program) () in
  Matcher.build ?scorers old_trace new_trace
