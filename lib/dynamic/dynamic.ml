module Tracer = Tracer

module Runtime = Runtime

module Matcher = Matcher

module CompilationContext = Tracer.CompilationContext

module Concrete = Concrete

type scoring_function = Matcher.sanitized_state -> Matcher.sanitized_state -> float option

let build_alignment ?compilation_env ?scorers ~deps ~old_program ~new_program =
  let compilation_env =
    match compilation_env with
    | Some env -> env
    | None -> Tracer.CompilationContext.init () in
  let build_bitrace = Tracer.bitrace compilation_env (deps, old_program) (deps, new_program) in
  fun () ->
    let old_trace, new_trace = build_bitrace () in
    Matcher.build ?scorers old_trace new_trace

let build_concrete_trace ?compilation_env ~deps program =
  let compilation_env =
    match compilation_env with
    | Some env -> env
    | None -> Tracer.CompilationContext.init () in
  let build_trace = Tracer.execution_trace compilation_env (deps, program) in
  let st = Random.get_state () in
  fun () ->
    let args, trace = build_trace ~st () in
    Concrete.build args trace
