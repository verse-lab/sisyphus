[@@@warning "-26-33-27"]
open Containers

let () =
  Printexc.register_printer (function
    | Env.Error (Lookup_error (loc, env, err)) ->
      Some (Format.to_string (fun fmt () -> Env.report_lookup_error loc env fmt err) ())
    | Symtable.(Error (Undefined_global global)) -> Some ("error: undefined global " ^ global)
    | _ -> None
  )

let parse_raw lexbuf =
  let result = Parser.implementation Lexer.token lexbuf in
  result
let parse_raw_expr lexbuf =
  let result = Parser.parse_expression Lexer.token lexbuf in
  result

let raw_parse_expr_str str = parse_raw_expr (Lexing.from_string ~with_positions:true str)
let raw_parse_expr_channel chan = parse_raw_expr (Lexing.from_channel ~with_positions:true chan)
let raw_parse_str str = parse_raw (Lexing.from_string ~with_positions:true str)
let raw_parse_channel chan = parse_raw (Lexing.from_channel ~with_positions:true chan)

module Backend = struct
  (* See backend_intf.mli. *)

  let symbol_for_global' = Compilenv.symbol_for_global'
  let closure_symbol = Compilenv.closure_symbol

  let really_import_approx = Import_approx.really_import_approx
  let import_symbol = Import_approx.import_symbol

  let size_int = Arch.size_int
  let big_endian = Arch.big_endian

  let max_sensible_number_of_arguments =
    (* The "-1" is to allow for a potential closure environment parameter. *)
    Proc.max_arguments_for_tailcalls - 1
end
let backend = (module Backend : Backend_intf.S)

type res = Ok of Obj.t | Err of string
type evaluation_outcome = Result of Obj.t | Exception of exn
external ndl_run_toplevel: string -> string -> res = "caml_natdynlink_run_toplevel"
let dll_run dll entry =
  match (try Result (Obj.magic (ndl_run_toplevel dll entry)) with exn -> Exception exn) with
  | Exception _ as r -> r
  | Result r ->
    match Obj.magic r with
    | Ok x -> Result x
    | Err s -> failwith ("dll_run failed: " ^ s)

let load_lambda phrase_name module_ident lam size required_globals =
  let slam = Simplif.simplify_lambda lam in
  print_endline @@ Format.to_string Printlambda.lambda slam;
  let dll = Filename.temp_file ("caml" ^ phrase_name) Config.ext_dll in
  let filename = Filename.chop_extension dll in
  let program = {
    Lambda.
    code = slam;
    main_module_block_size = size;
    module_ident;
    required_globals;
  } in
  let need_symbol sym =
    Option.is_none (Dynlink.unsafe_get_global_value ~bytecode_or_asm_symbol:sym) in
  let middle_end = Closure_middle_end.lambda_to_clambda in
  Asmgen.compile_implementation ~toplevel:need_symbol
    ~backend ~filename ~prefixname:filename
    ~middle_end ~ppf_dump:Format.str_formatter program;
  Asmlink.call_linker_shared [filename ^ Config.ext_obj] dll;
  Sys.remove (filename ^ Config.ext_obj);
  let dll =
    if Filename.is_implicit dll
    then Filename.concat (Sys.getcwd ()) dll
    else dll in
  let res = dll_run dll phrase_name in
  (try Sys.remove dll with Sys_error _ -> ());
  res


let remembered = ref Ident.empty

let rec remember phrase_name i = function
  | [] -> ()
  | Types.Sig_value  (id, _, _) :: rest
  | Sig_module (id, _, _, _, _) :: rest
  | Sig_typext (id, _, _, _) :: rest
  | Sig_class  (id, _, _, _) :: rest ->
      remembered := Ident.add id (phrase_name, i) !remembered;
      remember phrase_name (succ i) rest
  | _ :: rest -> remember phrase_name i rest


let global_symbol id =
  let sym = Compilenv.symbol_for_global id in
  match Dynlink.unsafe_get_global_value ~bytecode_or_asm_symbol:sym with
  | None ->
    failwith ("Opttoploop.global_symbol " ^ (Ident.unique_name id))
  | Some obj -> obj

let toplevel_value id =
  try Ident.find_same id !remembered
  with _ -> Misc.fatal_error @@ "Unknown ident: " ^ Ident.unique_name id

let toplevel_value id =
  let glob, pos = toplevel_value id in
  (Obj.magic (global_symbol glob)).(pos)

let fresh_phrase_name =
  let seqid = ref 0 in
  fun () ->
    incr seqid;
    Printf.sprintf "TOP%d" !seqid

let execute_mod env modl =
    (* print_endline @@ "module env: [" ^ String.concat ", " (List.map (fun id -> Ident.name id) Env.(diff empty env)) ^ "]"; *)
    let phrase_name = fresh_phrase_name () in
    Compilenv.reset ?packname:None phrase_name;
    Typecore.reset_delayed_checks ();
    let (str, sg, names, newenv) = Typemod.type_structure env modl in
    (* print_endline @@ "typed env: [" ^ String.concat ", " (List.map (fun id -> Ident.name id) Env.(diff env newenv)) ^ "]"; *)
    let sg' = Typemod.Signature_names.simplify newenv names sg in
    ignore (Includemod.signatures newenv ~mark:Mark_positive sg sg');
    Typecore.force_delayed_checks ();
    let module_ident, res, required_globals, size =
      let size, res = Translmod.transl_store_phrases phrase_name str in
      Ident.create_persistent phrase_name, res, Ident.Set.empty, size in
    Warnings.check_fatal ();
    let res = load_lambda phrase_name module_ident res size required_globals in
    (* print_endline @@ "registering opaque: " ^ (Ident.name module_ident); *)

    (* IMPORTANT: otherwise, will complain about no cmx files found for dyn-linked modules  *)
    Compilenv.record_global_approx_toplevel ();

    res, newenv

let open_mod_ast file =
  let file = Load_path.find file in
  let chan = open_in file in
  let mod_ast =
    Fun.protect
      ~finally:(fun () -> close_in_noerr chan)
      (fun () -> raw_parse_channel chan) in
  let output_prefix = Filename.remove_extension (Filename.basename file) in
  let modname = String.capitalize_ascii output_prefix in
  Parsetree.(
    Ast_helper.[
      Str.module_ (Mb.mk
                     (Location.mknoloc (Some modname))
                     (Mod.structure mod_ast)
                  )
    ]
  )

let () =
  (* Sys.interactive := true; *)
  (* Compmisc.init_path (); *)
  (* Clflags.dlcode := true; *)

  Clflags.native_code := true;  (* important, otherwise will crash *)
  (* Compmisc.read_clflags_from_env (); *)
  Compmisc.init_path ~dir:"../../_build/default/resources/seq_to_array/" ();

  (* let load_path =
   *   let expand = Misc.expand_directory Config.standard_library in
   *   List.concat [
   *   List.map expand (List.rev !Compenv.first_include_dirs);
   *   List.map expand (List.rev !Clflags.include_dirs);
   * 
   *   List.map expand (List.rev !Compenv.last_include_dirs);
   *   ["../../_build/default/resources/seq_to_array/"];
   *   Load_path.get_paths ()
   * ] in *)
  (* Load_path.init load_path;
   * Dll.add_path load_path; *)
  (* Load_path.add_dir "../../_build/default/resources/seq_to_array/"; *)
  (* List.iteri (Printf.printf "%d: %s\n") (Load_path.get_paths ());
   * Sys.interactive := true;
   * let crc_intfs = Symtable.init_toplevel() in
   * Env.import_crcs ~source:Sys.executable_name crc_intfs; *)
  let env = Compmisc.initial_env () in
  let ast = open_mod_ast "common.ml" in
  let res, env = execute_mod env ast in

  let ast = open_mod_ast "seq_to_array_old.ml" in
  let res, env = execute_mod env ast in


  
  (* let common, env = 
   *   let prog =
   *     let chan = open_in "../../_build/default/resources/seq_to_array/common.ml" in
   *     raw_parse_channel chan in
   *   Compilenv.reset ~packname:"Common"  "Common";
   *   Typecore.reset_delayed_checks ();
   *   let (str, sg, names, newenv) = Typemod.type_toplevel_phrase env prog in
   *   print_endline @@ Format.to_string Printtyped.implementation str;
   *   let sg' = Typemod.Signature_names.simplify newenv names sg in
   *   let coercion = (Includemod.signatures newenv ~mark:Mark_positive sg sg') in
   *   Typecore.force_delayed_checks ();
   *   Translmod.transl_toplevel_definition str, newenv in
   * Warnings.check_fatal (); *)


  print_endline "hello heloo hello...";
  ()
