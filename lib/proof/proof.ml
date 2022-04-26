module SP = Serapi.Serapi_protocol

let fb_handler fmt =
  let open Sertop.Sertop_init in
  fun (fb : Feedback.feedback) ->
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

let init () =
  let open Sertop.Sertop_init in
  let dft_ml_path, vo_path =
    Serapi.Serapi_paths.coq_loadpath_default ~implicit:true ~coq_path:Coq_config.coqlib in
  let ml_path = dft_ml_path in
  let vo_path = (
    Loadpath.{
      unix_path="../../_build/default/resources/seq_to_array/";
      coq_path = Names.DirPath.make [Names.Id.of_string "Proofs"];
      implicit=true;
      has_ml=true;
      recursive=true;
    }
  ) :: vo_path in

  (* coq initialization *)
  coq_init
    { fb_handler
    ; ml_load = None
    ; debug = true
    ; allow_sprop = true
    ; indices_matter = false
    ; ml_path
    ; vo_path
    } Caml.Format.err_formatter;
  (* document initialization *)

  let stm_options = Stm.AsyncOpts.default_opts in

  (* Disable due to https://github.com/ejgallego/coq-serapi/pull/94 *)
  let stm_options =
    { stm_options with
      async_proofs_tac_error_resilience = FNone
    ; async_proofs_cmd_error_resilience = false
    } in

  let injections = [
    Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some false);
    Coqargs.RequireInjection ("Proofs.Verify_seq_to_array_utils", None, Some false)
  ] in

  let sertop_dp = Names.(DirPath.make [Id.of_string "PyTop"]) in
  let doc_type = Stm.Interactive (TopLogical sertop_dp) in

  let ndoc = { Stm.doc_type
             ; injections
             ; stm_options
             } in

  let _ = Stm.new_doc ndoc in
  ()

let exec_cmd =
  let st_ref = ref (SP.State.make ()) in
  fun cmd ->
    try
      let ans, st = SP.exec_cmd !st_ref cmd in
      st_ref := st;
      ans
    with exn ->
      let msg = Caml.Printexc.to_string exn in
      [SP.ObjList [ SP.CoqString ("Exception raised in Coq: " ^ msg) ]]


let print_responses responses =
  List.iter (function
    | SP.Ack -> Format.printf "ack\n"
    | Completed -> Format.printf "completed\n"
    | Added (id, l, fcs) ->
      Format.printf "added(%a,%a)\n"
        Pp.pp_with (Stateid.print id)
        Pp.pp_with (Loc.pr l)
    | Canceled _ -> Format.printf "cancelled\n"
    | ObjList objs ->
      List.iter (function
        | SP.CoqGoal (goals) ->
          Format.printf "got %d goals\n"
            (List.length goals.goals);
          List.iteri (fun i (v: _ Serapi.Serapi_goals.reified_goal) ->
            Format.printf "\tgoal[%d]: %a\n"
              i Pp.pp_with (Constr.debug_print v.ty)
          ) goals.goals;

        | _ -> ()
      ) objs;

      
      Format.printf "objlist(%a)\n"
        (Format.pp_print_list Pp.pp_with)
        (List.map (SP.gen_pp_obj Environ.empty_env Evd.empty) objs)
    | CoqExn exn ->
      Format.printf "coqexn(\"%s\")\n" exn.str
  ) responses

let f () =
  init ();

  print_responses @@ exec_cmd SP.(Add (
    {lim=None; ontop=None; newtip=None; verb=false},
    "Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import Verify_seq_to_array_utils.
From Proofs Require Import Seq_to_array_old_ml.
")
  );

  print_responses @@ exec_cmd SP.(Add (
    {lim=None; ontop=None; newtip=None; verb=false},
    "Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.")
  );

  (* print_responses @@ exec_cmd SP.(Add (
   *   {lim=None; ontop=None; newtip=None; verb=false},
   *   "Show.")
   * );
   * 
   * print_responses @@ exec_cmd SP.(Exec (Stateid.of_int 9)); *)
  print_responses @@ exec_cmd SP.(Exec (Stateid.of_int 8));

  print_responses @@ exec_cmd SP.(Query (
    {preds=[]; limit=None; sid=Stateid.of_int 8;
     pp={
       pp_format=PpSer;
       pp_depth=100;
       pp_elide="...";
       pp_margin=80
     };
     route=Feedback.default_route;
    },
    Goals)
  );


  ()
