open Containers
open Bos

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Configuration module for Sisyphus" "config"))

let update_opt opt vl =
  opt := (Option.value ~default:!opt vl)

let validate_with_z3 = ref true
let max_z3_calls = ref None
let z3_default_timeout = ref 100
let z3_challenging_timeout = ref 15_000
let inner_dump_dir = ref None

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



let initialize ?default_timeout ?challenging_timeout ?max_calls ?filter_logs ?should_validate_with_z3 ?log_level ?log_dir ?dump_dir () =
  update_opt z3_default_timeout default_timeout;
  update_opt z3_challenging_timeout challenging_timeout;
  update_opt validate_with_z3 should_validate_with_z3;
  max_z3_calls := Option.or_ ~else_:!max_z3_calls max_calls;

  Logs.set_level ~all:true log_level;

  let () = match dump_dir with
    | None -> ()
    | Some path ->
      ensure_exists_dir path;
      inner_dump_dir := Some path
  in

  let reporter =
    match log_dir with
    | Some path ->
      ensure_exists_dir path;
      let log_file = with_fresh_log path in
      let oc = open_out log_file in
      let fmt = Format.of_chan oc in
      pretty_reporter fmt
      (* Logs_fmt.reporter ~app:fmt ~dst:fmt ()  *)
    | None -> Logs_fmt.reporter () in
  let reporter = match filter_logs with
    | None -> reporter
    | Some log_regx ->
      let log_regx = Re.Pcre.re ~flags:([`ANCHORED; `CASELESS]) log_regx
                     |> Re.compile in
      let matches = Re.execp log_regx in
      filter_reporter matches reporter in

  Logs.set_reporter reporter

let validate_with_z3 () = !validate_with_z3

let z3_default_timeout () = !z3_default_timeout

let z3_challenging_timeout () = !z3_challenging_timeout

let max_z3_calls () = !max_z3_calls

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
      


  
