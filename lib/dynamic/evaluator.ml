[@@@warning "-26-33-27"]
open Containers

let () =
  Printexc.register_printer (function
    | Env.Error (Lookup_error (loc, env, err)) ->
      Some (Format.to_string (fun fmt () -> Env.report_lookup_error loc env fmt err) ())
    | Symtable.(Error (Undefined_global global)) -> Some ("error: undefined global " ^ global)

    | Typecore.Error (loc, env, error) ->
      Some (Format.to_string Location.print_report (Typecore.report_error ~loc env error))
    | _ -> None
  )

let parse_raw lexbuf =
  let result = Parser.implementation Lexer.token lexbuf in
  result
let parse_expr_raw lexbuf =
  let result = Parser.parse_expression Lexer.token lexbuf in
  result


let raw_parse_str str = parse_raw (Lexing.from_string ~with_positions:true str)
let raw_parse_expr_str str = parse_expr_raw (Lexing.from_string ~with_positions:true str)
let raw_parse_channel chan = parse_raw (Lexing.from_channel ~with_positions:true chan)

module Internal = struct

  (** This module is filled with crazy OCaml runtime dark magic. I
      myself barely have a good grasp of how it fully works.

      Be careful when messing with this module...  *)

  let () =
    Clflags.native_code := true;
      Compmisc.init_path ()
  (* important, otherwise will crash *)


  module Backend = struct

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

  type res = Ok of Obj.t | Err of string
  [@@warning "-37"]

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
      ~backend:(module Backend : Backend_intf.S) ~filename ~prefixname:filename
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

  let global_symbol id =
    let sym = Compilenv.symbol_for_global id in
    match Dynlink.unsafe_get_global_value ~bytecode_or_asm_symbol:sym with
    | None ->
      failwith ("global_symbol " ^ (Ident.unique_name id) ^ " not found")
    | Some obj -> obj

  let toplevel_value id =
    let glob, pos = Translmod.nat_toplevel_name id in
    (Obj.magic (global_symbol glob)).(pos)

  let fresh_phrase_name =
    let seqid = ref 0 in
    fun () ->
      incr seqid;
      Printf.sprintf "TOP%d" !seqid

  let type_phrase env modl =
    let phrase_name = fresh_phrase_name () in
    Compilenv.reset ?packname:None phrase_name;
    Typecore.reset_delayed_checks ();
    let (str, sg, names, newenv) = Typemod.type_structure env modl in
    let sg' = Typemod.Signature_names.simplify newenv names sg in
    Typecore.force_delayed_checks ();
    Compilenv.record_global_approx_toplevel ();
    str, sg', newenv

  let execute_phrase env modl =
    let phrase_name = fresh_phrase_name () in
    Compilenv.reset ?packname:None phrase_name;
    Typecore.reset_delayed_checks ();
    let (str, sg, names, newenv) = Typemod.type_structure env modl in
    let sg' = Typemod.Signature_names.simplify newenv names sg in
    ignore (Includemod.signatures newenv ~mark:Mark_positive sg sg');
    Typecore.force_delayed_checks ();

    let module_ident, res, required_globals, size =
      let size, res = Translmod.transl_store_phrases phrase_name str in
      Ident.create_persistent phrase_name, res, Ident.Set.empty, size in
    Warnings.check_fatal ();
    let res = load_lambda phrase_name module_ident res size required_globals in

    (* IMPORTANT: otherwise, will complain about no cmx files found for dyn-linked modules  *)
    Compilenv.record_global_approx_toplevel ();

    sg', res, newenv

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

  let dyn_load_definition_as_module env ~mod_name ~ast =
    let ast =
      Parsetree.(
        Ast_helper.[
          Str.module_ (Mb.mk
                         (Location.mknoloc (Some mod_name))
                         (Mod.structure ast)
                      )
        ]
      ) in
    let _, res, env = execute_phrase env ast in
    match res with
    | Result _ -> env
    | Exception e -> raise e

  let dyn_load_module_from_file env file =
    let ast = open_mod_ast file in
    let _, res, env = execute_phrase env ast in
    match res with
    | Result _ -> env
    | Exception e -> raise e

  let add_static_module_def env ~mod_name ~ast = 
    let dyn_global_sig, sg, _ =
      ast |> type_phrase env in
    let cmt : Cmi_format.cmi_infos = {
      cmi_name=mod_name;
      cmi_sign=sg;
      cmi_crcs=[];
      cmi_flags=[];
    } in    
    let old_loader = !Persistent_env.Persistent_signature.load in
    Persistent_env.Persistent_signature.load := (fun ~unit_name ->
      if String.equal mod_name unit_name
      then Some (Persistent_env.Persistent_signature.{filename=String.lowercase_ascii mod_name ^ ".cmi"; cmi=cmt})
      else old_loader ~unit_name;
    );
    Env.add_persistent_structure (Ident.create_persistent mod_name) env

  let eval_expr env expr =
    let expr = 
      let pat = Ast_helper.Pat.var (Location.mknoloc "_$") in
      let vb = Ast_helper.Vb.mk pat expr in
      Ast_helper.[
        Str.value Asttypes.Nonrecursive [vb]
      ] in
    let sg, outcome, env = execute_phrase env expr in

    match outcome with
    | Exception e -> raise e
    | Result _ ->
      match sg with
      | Types.[ Sig_value (id, _, _) ] ->
        toplevel_value id
      | _ -> assert false
end


type env = Env.t

let initial_env () = Compmisc.initial_env ()

include Internal
