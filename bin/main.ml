[@@@warning "-33"]
open Containers

let generate_proof_script log_level log_dir log_filter dump_dir coq_verbose
      disable_z3_validation z3_default_timeout z3_challenging_timeout max_z3_calls
      deps coq_deps old_program new_program
      coq_dir coq_lib_name
      old_proof new_proof_base new_proof_name =

  Random.init 2;

  Configuration.initialize
    ?log_level ?log_dir ?dump_dir 
    ?filter_logs:log_filter
    ?default_timeout:z3_default_timeout
    ?challenging_timeout:z3_challenging_timeout ?max_calls:max_z3_calls
    ~should_validate_with_z3:(not disable_z3_validation) ();

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

let disable_z3_validation =
  Arg.(
    value @@
    flag
      (info ~doc:"$(opt) indicates whether sisyphus should disable its \
                  validate candidate invariants using Z3. Can also be \
                  provided through the $(env) ENV variable (as 1 to \
                  disable Z3 and 0 to enable it (default))."
         ~env:(env_var "SIS_DISABLE_Z3") ["disable-z3"])
  )

let max_z3_calls =
  Arg.(value @@
       opt
         (some int)
         None
         (info
            ~doc:"$(docv) specifies the maximum number of calls to Z3 \
                  that Sisyphus will perform while generating \
                  invariants. If this option is combined with the \
                  DISABLE_Z3_VALDIATION flag, then Z3 validation will \
                  still be performed, but only $(docv) calls will be \
                  made before assuming that the next candidate is \
                  true. Can also be specified by the $(env) ENV \
                  variable."
            ~env:(env_var "SIS_MAX_Z3_CALLS")
            ~docv:"MAX_Z3_CALLS"
            ["m"; "max-z3-calls"]))

let z3_default_timeout =
  Arg.(
    value @@
    opt (some int) None
      (info ~docv:"Z3_BASE_TIMEOUT"
         ~doc:"$(docv) defines the timeout used for Z3 on simple \
               instances. Can also be provided through the $(env) ENV \
               variable."
         ~env:(env_var "SIS_Z3_BASE_TIMEOUT") ["z3-base-timeout"])
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
                 $ disable_z3_validation
                 $ z3_default_timeout
                 $ z3_challenging_timeout
                 $ max_z3_calls
                 $ deps
                 $ coq_deps
                 $ old_program
                 $ new_program
                 $ coq_dir
                 $ coq_lib_name
                 $ old_proof_name
                 $ new_proof_base
                 $ output_file, sisyphus_info)))

