[@@@warning "-33"]
open Containers


let generate_proof_script coq_verbose deps old_program new_program  coq_dir coq_lib_name old_proof new_proof_base new_proof_name =

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
  let ctx = (Coq.Proof.make ~verbose:coq_verbose [
    Coq.Coqlib.make ~path:(coq_dir) coq_lib_name
  ] ) in
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
    | `Error e -> `Error e
    | `Ok s ->
      match Fpath.of_string s with
      | Ok v -> `Ok v
      | Error (`Msg e) -> `Error e in
  let printer fmt vl = Fpath.pp fmt vl in
  (parser, printer)

let coq_verbose =
  Arg.value @@ Arg.flag (Arg.info
              ~doc:"$(docv) indicates whether Sisyphus should run Coq with verbose output"
              ~docv:"COQ_VERBOSE"
              ["cv"; "coq-verbose"])
            
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
                 $ coq_verbose
                 $ deps
                 $ old_program
                 $ new_program
                 $ coq_dir
                 $ coq_lib_name
                 $ old_proof_name
                 $ new_proof_base
                 $ output_file, sisyphus_info)))

