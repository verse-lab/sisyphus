open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Main runner for Sisyphus" "runner"))

let generate_proof_script log_level log_dir log_filter dump_dir coq_verbose print_extraction_steps
      dump_generated_invariants
      disable_tactic_validation solver_tactic max_solve_calls
      deps coq_deps old_program new_program
      coq_dir coq_lib_name
      old_proof new_proof_base new_proof_name =

  Random.init 2;

  Configuration.initialize
    ?log_level ?log_dir ?dump_dir
    ~print_proof_extraction:print_extraction_steps
    ~dump_generated_invariants
    ?filter_logs:log_filter
    ~dispatch_goals_with_tactic:(not disable_tactic_validation)
    ?solver_tactic:solver_tactic
    ?max_dispatch_attempts:max_solve_calls
    ();

  let old_program = Bos.OS.File.read old_program |> Result.get_exn in
  let new_program = Bos.OS.File.read new_program |> Result.get_exn in


  let env = Dynamic.CompilationContext.init () in
  let old_program = Lang.Sanitizer.parse_str old_program in
  let new_program = Lang.Sanitizer.parse_str new_program in
  let alignment =
    Dynamic.build_alignment ~compilation_env:env
      ~deps ~old_program ~new_program () in
  let concrete =
    Dynamic.build_concrete_trace ~compilation_env:env
      ~deps new_program in
  let ctx = (Coq.Proof.make ~verbose:coq_verbose (
      List.map (fun (lib_name, lib_dir) -> Coq.Coqlib.make ~path:(lib_dir) lib_name)
        ((coq_lib_name, coq_dir) :: coq_deps)
    )) in
  let old_proof =
    Bos.OS.File.read Fpath.(coq_dir / old_proof)
    |> Result.get_exn
    |> Proof_parser.Parser.parse ctx in
  let new_proof_base =
    Bos.OS.File.read Fpath.(coq_dir / new_proof_base)
    |> Result.get_exn in
  let ctx =
    Proof_generator.Proof_context.init
      ~compilation_context:env ~old_proof ~new_proof_base
      ~alignment ~concrete ~ctx in
  let new_proof =
    (new_proof_base ^ "\n" ^ Proof_generator.Generator.generate
       ~logical_mappings:old_program.logical_mappings ctx
       new_program) in
  Log.info (fun f -> f "%s\n%s\n%s" (String.make 20 '=') new_proof (String.make 20 '='));
  Bos.OS.File.write Fpath.(coq_dir / new_proof_name)
    new_proof
  |> Result.get_exn


open Cmdliner

let fpath =
  let (parser, printer) = Arg.file in
  let parser s =
    match parser s with
    | `Error e -> Error (`Msg e)
    | `Ok s -> Fpath.of_string s in
  let printer fmt vl = Fpath.pp fmt vl in
  Arg.conv (parser, printer)

let log_level =
  let parse s =
    match String.lowercase_ascii s with
    | "debug" -> Ok Logs.Debug
    | "info" -> Ok Logs.Info
    | "warning" | "warn" -> Ok Logs.Warning
    | "error" | "err" -> Ok Logs.Error
    | "app" -> Ok Logs.App
    | _  ->
      Error (`Msg (Format.sprintf
                     "could not convert %s into a log level (expected \
                      one of debug, info, warning, error, app)"
                     s)) in
  Arg.conv (parse,Logs.pp_level)

let log_level =
  Arg.(value @@
       opt
         (some log_level)
         None
         (info
            ~doc:"$(docv) specifies the logging level that Sisyphus \
                  should output. Should be one of (debug, info, \
                  warning, error, app). Can also be specified by the \
                  $(env) ENV variable."
            ~env:(env_var "SIS_LOG_LEVEL")
            ~docv:"LOG_LEVEL"
            ["l"; "log-level"]))

let log_filter =
  Arg.(value @@
       opt
         (some string)
         None
         (info
            ~doc:"$(docv) specifies a regular expression \
                  (PCRE-compatible) to filter logging output from \
                  Sisyphus. Only logging sources that match the regex \
                  will be output. Can also be specified by the $(env) \
                  ENV variable."
            ~env:(env_var "SIS_LOG_FILTER")
            ~docv:"LOG_FILTER"
            ["f"; "log-filter"]))

let log_dir =
  Arg.(value @@
       opt
         (some fpath)
         None
         (info
            ~doc:"$(docv) specifies a directory to which Sisyphus \
                  logging output should be placed. Can also be \
                  specified by the $(env) ENV variable."
            ~env:(env_var "SIS_LOG_DIR")
            ~docv:"LOG_DIR"
            ["L"; "log-dir"]))

let dump_dir =
  Arg.(value @@
       opt
         (some fpath)
         None
         (info
            ~doc:"$(docv) specifies a directory to which Sisyphus \
                  should dump intermediate outputs. Can also be \
                  specified by the $(env) ENV variable."
            ~env:(env_var "SIS_DUMP_DIR")
            ~docv:"DUMP_DIR"
            ["dump-dir"]))


let coq_verbose =
  Arg.value @@ Arg.flag (Arg.info
                           ~doc:"$(docv) indicates whether Sisyphus should run Coq with verbose output"
                           ~docv:"COQ_VERBOSE"
                           ["cv"; "coq-verbose"])

let print_extraction_steps =
  Arg.(
    value @@
    flag
      (info ~doc:"$(opt) indicates whether sisyphus should dump \
                  detailed information on its proof reduction and \
                  analysis phases.  Can also be provided through the \
                  $(env) ENV variable (as 1 to dump steps and 0 to \
                  disable it (default))."
         ~env:(env_var "SIS_DUMP_EXTRACTION") ["dump-extraction"])
  )

let dump_generated_invariants =
  Arg.(
    value @@
    flag
      (info ~doc:"$(opt) indicates whether sisyphus should dump \
                  generated invariants to the DUMP_DIR directory.  Can \
                  also be provided through the $(env) ENV variable (as \
                  1 to dump invariants and 0 to disable it (default))."
         ~env:(env_var "SIS_DUMP_INVARIANTS") ["dump-invariants"])
  )


let disable_tactic_validation =
  Arg.(
    value @@
    flag
      (info ~doc:"$(opt) indicates whether sisyphus should disable its \
                  validation of candidate invariants using its solver \
                  tactic. Can also be provided through the $(env) ENV \
                  variable (as 1 to disable Z3 and 0 to enable it \
                  (default))."
         ~env:(env_var "SIS_DISABLE_SOLVER") ["disable-solver"])
  )

let max_solve_calls =
  Arg.(value @@
       opt
         (some int)
         None
         (info
            ~doc:"$(docv) specifies the maximum number of attempts \
                  that Sisyphus will do to find a solvable invariant \
                  before using admits. Defaults to 3."
            ~env:(env_var "SIS_MAX_SOLVER_CALLS")
            ~docv:"MAX_SOLVER_CALLS"
            ["m"; "max-solver-calls"]))

let solver_tactic =
  Arg.(
    value @@
    opt (some string) None
      (info ~docv:"SOLVER_TACTIC"
         ~doc:"$(docv) defines the tactic used by Sisyphus to dispatch \
               generated subgoals (and thereby validate \
               candidates). Can also be provided through the $(env) \
               ENV variable. Defaults to \"sis_generic_solver\"."
         ~env:(env_var "SIS_SOLVER_TACTIC") ["solver-tactic"])
  )

let z3_challenging_timeout =
  Arg.(
    value @@
    opt (some int) None
      (info ~docv:"Z3_CHALLENGING_TIMEOUT"
         ~doc:"$(docv) defines the timeout used for Z3 on challenging \
               instances. Can also be provided through the $(env) ENV \
               variable."
         ~env:(env_var "SIS_Z3_CHALLENGING_TIMEOUT") ["z3-challenging-timeout"])
  )


let enable_debug =
  Arg.value @@ Arg.flag (Arg.info
                           ~doc:"$(docv) indicates whether Sisyphus should run Coq with verbose output"
                           ~docv:"DEBUG"
                           ["cv"; "coq-verbose"])

let coq_deps =
  Arg.(value @@
       opt_all (t2 ~sep:':' string fpath) []
         (info
            ~doc:"$(docv) declares a pair of NAME:PATH that will be \
                  used to instantiate the Coq process inside \
                  Sisyphus. This argument can be passed multiple times \
                  and can be thought of as functionally equivalent to \
                  -R PATH NAME."
            ~docv:"COQ_DEP" ["c"; "coqdep"])
      )

let deps =
  Arg.value @@
  Arg.opt_all Arg.file []
    (Arg.info
       ~doc:"$(docv) declares an ml file that the project depends on to build and run."
       ~docv:"ML_DEP"
       ["d"; "dep"]
    )

let old_program =
  Arg.(required @@ pos 0 (some fpath) None
         (info
            ~doc:"$(docv) is the path to the source code of the old program."
            ~docv:"OLD_PROGRAM"
            []
         ))


let new_program =
  Arg.(required @@ pos 1 (some fpath) None
         (info
            ~doc:"$(docv) is the path to the source code of the new program."
            ~docv:"NEW_PROGRAM"
            []
         ))

let coq_dir =
  Arg.(required @@ pos 2 (some fpath) None
         (info
            ~doc:"$(docv) is the path to the root of the coq library under which the proof lives."
            ~docv:"COQ_DIR"
            []
         ))

let coq_lib_name =
  Arg.(required @@ pos 3 (some string) None
         (info
            ~doc:"$(docv) is the name of the coq library in which the proof should live."
            ~docv:"COQ_LIB_NAME"
            []
         ))

let old_proof_name =
  Arg.(required @@ pos 4 (some string) None
         (info
            ~doc:"$(docv) is the file name of old proof, should be found under COQ_DIR."
            ~docv:"COQ_OLD_PROOF"
            []
         ))

let new_proof_base =
  Arg.(required @@ pos 5 (some string) None
         (info
            ~doc:"$(docv) is the file name of new proof stub, should be found under COQ_DIR."
            ~docv:"COQ_NEW_PROOF_STUB"
            []
         ))

let output_file =
  Arg.(required @@ pos 6 (some string) None
         (info
            ~doc:"$(docv) is the file name of new proof stub, should be found under COQ_DIR."
            ~docv:"COQ_OUT_FILE"
            []
         ))


let () =
  let sisyphus_info = Term.info "sisyphus" in
  Term.(exit (eval
                (const
                   generate_proof_script
                 $ log_level
                 $ log_dir
                 $ log_filter
                 $ dump_dir
                 $ coq_verbose
                 $ print_extraction_steps
                 $ dump_generated_invariants
                 $ disable_tactic_validation
                 $ solver_tactic
                 $ max_solve_calls
                 $ deps
                 $ coq_deps
                 $ old_program
                 $ new_program
                 $ coq_dir
                 $ coq_lib_name
                 $ old_proof_name
                 $ new_proof_base
                 $ output_file, sisyphus_info)))
