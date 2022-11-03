open Containers
open Bos

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Configuration module for Sisyphus" "config"))

let update_opt opt vl =
  opt := (Option.value ~default:!opt vl)

let sisyphus_solver_tactic = ref "sis_generic_solver"
let enable_tactic_based_goal_dispatch = ref true
let should_admit_all_sub_goals = ref false
let max_tactic_dispatch_attempts = ref 3

let inner_dump_dir = ref None
let inner_stats_out_file = ref None
let should_print_proof_extraction = ref false
let should_dump_generated_invariants = ref false

type stats =
  | Counter of int
  | TimerRunning of { cumulative_time: Ptime.Span.t; current_start: Ptime.t }
  | TimerStopped of Ptime.Span.t

let show_stat name = function
  | Counter i -> string_of_int i
  | TimerStopped t ->
    Ptime.Span.to_float_s t
    |> Format.sprintf "%.6f"
  | _ ->
    Format.ksprintf ~f:failwith "found invalid stat, perhaps you forgot to close! %s " name

let hstats : (string, stats) Hashtbl.t = Hashtbl.create 10

let pretty_reporter formatter =
  let report src level ~over k user's_callback =
    let level_style, level =
      match level with
      | Logs.App ->     `White,   "     "
      | Logs.Error ->   `Red,     "ERROR"
      | Logs.Warning -> `Yellow,  " WARN"
      | Logs.Info ->    `Green,   " INFO"
      | Logs.Debug ->   `Blue,    "DEBUG" in
    user's_callback @@ fun ?header:_ ?tags:_ format_and_arguments ->

    let time =
      let time = Ptime_clock.now () in
      let ((y, m, d), ((hh, mm, ss), _tz_offset_s)) =
        Ptime.to_date_time time in
      Printf.sprintf "%02i.%02i.%02i %02i:%02i:%02i."
        d m (y mod 100) hh mm ss in
    let source =
      let width = 5 in
      if String.equal (Logs.Src.name src) (Logs.Src.name Logs.default) then
        String.make width ' '
      else
        let name = Logs.Src.name src in
        if String.length name > width then
          String.sub name (String.length name - width) width
        else
          (String.make (width - String.length name) ' ') ^ name in
    let source_prefix, source =
      try
        let dot_index = String.rindex source '.' + 1 in
        String.sub source 0 dot_index,
        String.sub source dot_index (String.length source - dot_index)
      with Not_found ->
        "", source in

    let write _fmt = over (); k () in
    (* The formatting proper. *)
    Format.kfprintf write formatter
      ("%a %a%s %a @[" ^^ format_and_arguments ^^ "@]@.")
      Fmt.(styled `Faint string) time
      Fmt.(styled `White string) source_prefix source
      Fmt.(styled level_style string) level in
  {Logs.report}


let filter_reporter cond r =
  let report src level ~over k msgf =
    (* if matches the regex then report *)
    if cond (Logs.Src.name src)
    then r.Logs.report src level ~over k msgf
    else k ()
  in
  { Logs.report }

let ensure_exists_dir path =
  let open Result in
  match OS.Dir.create ~path:true path with
  | Ok _ -> ()
  | Error (`Msg msg) ->
    Format.ksprintf ~f:failwith
      "failed to create directory %a with error %s"
      Fpath.pp path msg

let with_fresh_log base_path =
  match begin
    let open Result in
    let now = Ptime_clock.now () in
    let file_name = Format.sprintf "[%a]-log" (Ptime.pp_human ()) now in
    let log_path = Fpath.(base_path / file_name) in
    let* _ = OS.File.write log_path "SISYPHUS LOG OUTPUT will go here" in
    return (Fpath.to_string log_path)
  end
  with
  | Ok v -> v
  | Error (`Msg msg) ->
    Format.ksprintf ~f:failwith
      "failed to create log file in %a with error %s"
      Fpath.pp base_path msg

let with_name_file base_path name =
  let open Result in
  let path = Fpath.(base_path / name) in
  let* exists = OS.Path.exists path in
  if not exists
  then return path
  else
    let rec loop i =
      let name = Format.sprintf "%s-%d" name i in
      let path = Fpath.(base_path / name) in
      let* exists = OS.Path.exists path in
      if not exists
      then return path
      else loop (i + 1) in
    loop 1

(* [combine r1 r2] combines two reporters and sends output to both of
   them. Taken from the logs documentation. *)
let combine r1 r2 =
  let report = fun src level ~over k msgf ->
    let v = r1.Logs.report src level ~over:(fun () -> ()) k msgf in
    r2.Logs.report src level ~over (fun () -> v) msgf in
  { Logs.report }

let initialize  ?filter_logs ?print_proof_extraction ?dump_generated_invariants ?log_level ?log_dir ?dump_dir
      ?dispatch_goals_with_tactic ?solver_tactic ?max_dispatch_attempts ?admit_all_sub_goals ?stats_out_file () =
  update_opt should_print_proof_extraction print_proof_extraction;
  update_opt should_dump_generated_invariants dump_generated_invariants;
  update_opt sisyphus_solver_tactic solver_tactic;
  update_opt enable_tactic_based_goal_dispatch dispatch_goals_with_tactic;
  update_opt max_tactic_dispatch_attempts max_dispatch_attempts;
  update_opt should_admit_all_sub_goals admit_all_sub_goals;

  Logs.set_level ~all:true log_level;

  let () = match dump_dir with
    | None -> ()
    | Some path ->
      ensure_exists_dir path;
      inner_dump_dir := Some path
  in

  let () = match stats_out_file with
    | None -> ()
    | Some path ->
      (* TODO: check if file path exists *)
      inner_stats_out_file := Some path
  in

  let reporter = Logs_fmt.reporter () in
  let reporter =
    match log_dir with
    | Some path ->
      ensure_exists_dir path;
      let log_file = with_fresh_log path in
      let oc = open_out log_file in
      let fmt = Format.of_chan oc in
      Format.flush fmt ();
      combine (pretty_reporter fmt) reporter
      (* Logs_fmt.reporter ~app:fmt ~dst:fmt ()  *)
    | None -> reporter in
  let reporter = match filter_logs with
    | None -> reporter
    | Some log_regx ->
      let log_regx = Re.Pcre.re ~flags:([`ANCHORED; `CASELESS]) log_regx
                     |> Re.compile in
      let matches = Re.execp log_regx in
      filter_reporter matches reporter in

  Logs.set_reporter reporter

let print_proof_extraction () = !should_print_proof_extraction

let dump_generated_invariants () = !should_dump_generated_invariants

let dump_output name f =
  match !inner_dump_dir with
  | None -> ()
  | Some base_path ->
    (*  *)
    match begin
      let open Result in
      let* path = with_name_file base_path name in
      let output = ref "NO-OUTPUT" in
      let fmt fmt =
        Format.ksprintf ~f:(fun s ->
          output := s
        ) fmt in
      f fmt;
      OS.File.write path !output
    end
    with
    | Ok _ -> ()
    | Error (`Msg m) ->
      Log.err (fun f -> f "failed to dump output with name %s with error %s" name m)

let dump_stats () =
  match !inner_stats_out_file with
  | None -> ()
  | Some base_path ->
    (*  *)
    match begin
      let output = Hashtbl.to_list hstats
                   |> List.map (fun (name, stat) -> Format.sprintf "%s: %s" name (show_stat name stat))
                   |> String.concat "\n" in
      OS.File.write base_path output
    end
    with
    | Ok _ -> ()
    | Error (`Msg m) ->
      Log.err (fun f -> f "failed to dump stats with with error %s" m)

let dispatch_goals_with_solver_tactic () = !enable_tactic_based_goal_dispatch

let solver_tactic () = !sisyphus_solver_tactic

let max_goal_dispatch_attempts () = !max_tactic_dispatch_attempts

let admit_all_sub_goals () = !should_admit_all_sub_goals

let stats_incr_count name =
  let f _  = function
    | None -> Some (Counter 1)
    | Some (Counter v) -> Some (Counter (v + 1))
    | _ -> Format.ksprintf ~f:failwith "tried to increment non-counter statistic %s" name in

  Hashtbl.update hstats ~f ~k:name

let stats_start_timer name =
  let start ct =
    Some (TimerRunning { cumulative_time = ct; current_start = Ptime_clock.now ()}) in
  let f _  = function
    | None -> start Ptime.Span.zero
    | Some (TimerStopped ct) -> start ct
    | _ -> Format.ksprintf ~f:failwith "tried to restart running timer %s" name in

  Hashtbl.update hstats ~f ~k:name

let stats_stop_timer name =
  let f _  = function
    | Some (TimerRunning { cumulative_time; current_start }) ->
      let end_time = Ptime_clock.now () in
      let diff = Ptime.diff end_time current_start in
      let cumulative_time = Ptime.Span.add cumulative_time diff in
      Some (TimerStopped cumulative_time)
    | _ -> Format.ksprintf ~f:failwith "tried to restart running timer %s" name in

  Hashtbl.update hstats ~f ~k:name


let stats_time name f =
  stats_start_timer name;
  let res = f () in
  stats_stop_timer name;
  res
