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

let v = Sisyphus_dynamic_global.trace
let () =
  Clflags.native_code := true;  (* important, otherwise will crash *)
  Compmisc.init_path ~dir:"../../_build/default/lib/dynamic/" ();
  Compmisc.init_path ~dir:"../../_build/default/resources/seq_to_array/" ();

  let dyn_global_sig, sg, _ = [%blob "./sisyphus_dynamic_global.ml"]
             |> raw_parse_str
             |> type_phrase (Compmisc.initial_env ()) in

  let cmt : Cmi_format.cmi_infos = {
    cmi_name="Sisyphus_dynamic_global";
    cmi_sign=sg;
    cmi_crcs=[];
    cmi_flags=[];
  } in
  let old_loader = !Persistent_env.Persistent_signature.load in
  Persistent_env.Persistent_signature.load := (fun ~unit_name ->
    match unit_name with
    | "Sisyphus_dynamic_global" ->
      Some (Persistent_env.Persistent_signature.{filename="sisyphus_dynamic_global.cmi"; cmi=cmt})
    | _ -> old_loader ~unit_name;
  );

  for _ = 0 to 2 do


    let env = Compmisc.initial_env () in
      
    let env = Env.add_persistent_structure (Ident.create_persistent "Sisyphus_dynamic_global") env in

    let ast = open_mod_ast "common.ml" in
    let _, res, env = execute_phrase env ast in

    let ast = open_mod_ast "seq_to_array_old.ml" in
    let _, res, env = execute_phrase env ast in

    (* let _, ty = Env.lookup_type
     *            ~loc:(Location.mknoloc ()).loc
     *            (Option.get_exn_or "could not parse stdlib" @@ Longident.unflatten ["Stdlib"; "ref"]) env in *)


    let v = (module (struct
              type t = YouCantSeeThis of int * t list

              let rec to_string = function
                | YouCantSeeThis (cnt, children) ->
                  "YouCantSeeThis" ^ string_of_int cnt ^ "(" ^ (String.concat ", " (List.map to_string children)) ^ ")"

              let create () = YouCantSeeThis(10, [])

              let rec update (YouCantSeeThis (vl,children)) n =
                YouCantSeeThis (vl, YouCantSeeThis (n, []) :: List.map (fun tree -> update tree (n + vl)) children)

            end): Sisyphus_dynamic_global.S) in

    let vl' : (module Sisyphus_dynamic_global.S) = eval_expr env (raw_parse_expr_str "(module (struct
              type t = YouCantSeeThis of int * t list

              let rec to_string = function
                | YouCantSeeThis (cnt, children) ->
                  \"YouCantSeeThis\" ^ string_of_int cnt ^ \"(\" ^ (String.concat \", \" (List.map to_string children)) ^ \")\"

              let create () = YouCantSeeThis(10, [])

              let rec update (YouCantSeeThis (vl,children)) n =
                YouCantSeeThis (vl, YouCantSeeThis (n, []) :: List.map (fun tree -> update tree (n + vl)) children)

            end): Sisyphus_dynamic_global.S)") in
    let module M = (val vl') in
    let datatype_str = M.create () |> Fun.flip M.update 10 |> Fun.flip M.update 20 |> M.to_string in
    print_endline @@ Printf.sprintf "%s"  datatype_str;

    (* let vl' : int ref =
     *   eval_expr (Env.add_module (Ident.create_predef "Dynamic") Types.Mp_absent
     *                Types.(Mty_signature [
     *                   Sig_value (
     *                    (Ident.create_predef "trace"), {
     *                      val_type={
     *                        desc=Tconstr (Path.Pdot (Pident (Ident.create_persistent "Stdlib"), "ref"), [
     *                          {
     *                            desc=Tconstr (Path.Pdot (Pident (Ident.create_persistent "Stdlib"), "int"), [], ref Mnil);
     *                            level=0;
     *                            scope=0;
     *                            id=0;
     *                          }
     *                        ], ref Mnil);
     *                        level=0;
     *                        scope=0;
     *                        id=0;
     *                      };
     *                      val_kind=Val_reg;
     *                      val_loc=(Location.mknoloc ()).loc;
     *                      val_attributes=[];
     *                      val_uid=Uid.internal_not_actually_unique
     *                     },
     *                     Types.Exported
     *                   )
     *                 ]) env) (raw_parse_expr_str "Dynamic.trace") in *)



    let a : int array = eval_expr env (raw_parse_expr_str "Seq_to_array_old.to_array Common.(fun () -> Cons (1, fun () -> Nil))") in

    begin match a with
    | a ->
      print_endline @@
      Printf.sprintf "{%s}" (Array.to_list a |> List.mapi (Printf.sprintf "[%d]: %d") |> String.concat ", ");
    end;
  done;
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
