module SP = Serapi.Serapi_protocol

let coq_initialised = ref None

module type CONFIG = sig
  val libs: Coqlib.t list
  val verbose: bool
end


module Make (C: CONFIG) = struct

  type state = State of Stateid.t [@@unboxed]

  let fb_handler =
    let open Sertop.Sertop_init in
    if C.verbose
    then
      fun fmt (fb : Feedback.feedback) ->
        let open Feedback in
        let open Caml.Format in
        let pp_lvl fmt lvl = match lvl with
          | Error   -> fprintf fmt "Error: "
          | Info    -> fprintf fmt "Info: "
          | Debug   -> fprintf fmt "Debug: "
          | Warning -> fprintf fmt "Warning: "
          | Notice  -> fprintf fmt ""
        in
        let pp_loc fmt loc = let open Loc in match loc with
        | None     -> fprintf fmt ""
        | Some loc ->
          let where = match loc.fname with InFile f -> f.file | ToplevelInput -> "Toplevel input" in
          fprintf fmt "\"%s\", line %d, characters %d-%d:@\n"
            where loc.line_nb (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos) in
        match fb.contents with
        | Processed ->
          fprintf fmt "Processed@\n%!"
        | ProcessingIn s ->
          fprintf fmt "Processing in %s@\n%!" s
        | FileLoaded (m,n) ->
          fprintf fmt "file_loaded: %s, %s@\n%!" m n
        | Message (lvl,loc,msg) ->
          fprintf fmt "@[%a@]%a@[%a@]\n%!" pp_loc loc pp_lvl lvl Pp.pp_with msg
        | _ -> ()
    else
      fun _fmt _fb -> ()

  (* coq initialization *)
  let state =
    let open Sertop.Sertop_init in
    let dft_ml_path, vo_path =
      Serapi.Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path:Coq_config.coqlib in
    let ml_path = dft_ml_path in
    let vo_path = List.map Coqlib.to_load_path C.libs @ vo_path in


    begin match !coq_initialised with
    | None ->
      coq_initialised := Some C.libs;
      coq_init {
        fb_handler;
        ml_load = None;
        debug = true;
        allow_sprop = true;
        indices_matter = false;
        ml_path;
        vo_path
      } Caml.Format.err_formatter
    | Some prev ->
      coq_initialised := Some C.libs;
      List.iter (fun elt -> Coqlib.path elt |> Fpath.to_string |> Loadpath.remove_load_path) prev;
      (* coq has already been initialised, just add the user supplied
         load paths to the environment *)
      List.iter (fun v -> v |> Coqlib.to_load_path |> Loadpath.add_vo_path) C.libs
    end;
    ref (SP.State.make ())

  let initial_state = State (Stateid.of_int 1)

  let _eval_cmd cmd =
    let answers, state' = SP.exec_cmd !state cmd in
    state := state';
    answers                           

  let fresh_doc () =
    ignore @@ _eval_cmd SP.(NewDoc {
      top_name=Coqargs.TopLogical Names.(DirPath.make [Id.of_string "SisyphusTop"]);
      require_libs=None;
      (* don't bother changing these, serapi doesn't actually read them anyway *)
      ml_load_path=None;
      vo_load_path=None
    })

  let () = fresh_doc ()

  let cancel states =
    let states = List.map (fun (State v) -> v) states in
    _eval_cmd SP.(Cancel states)
    |> List.map (function SP.Canceled st -> st | _ -> [])
    |> List.flatten
    |> List.map (fun v -> State v)

  let add ?state txt =
    let state = Option.map (fun (State v) -> v) state in
    _eval_cmd SP.(Add ({lim=None; ontop=state; newtip=None; verb=(* C.verbose *) true}, txt))
    |> List.filter_map (function
      | SP.Added (id, _, _) -> Some (State id)
      | _ -> None
    )

  let parse ?state txt =
    let state = Option.map (fun (State v) -> v) state in
    _eval_cmd SP.(Parse ({ontop=state}, txt))
    |> List.find_map (function
      | SP.(ObjList [CoqAst cast]) -> Some cast
      | _ -> None)

  let query (State state) cmd =
    _eval_cmd SP.(Query ({
      preds=[];
      limit=None;
      sid=state;
      pp={ pp_format=PpSer; pp_depth=100; pp_elide="..."; pp_margin=80 };
      route=Feedback.default_route;
    }, cmd))
    |> List.find_map (function
      | SP.(ObjList query) -> Some query
      | _ -> None)

  let exec (State state) =
    ignore @@ _eval_cmd SP.(Exec state)

end

