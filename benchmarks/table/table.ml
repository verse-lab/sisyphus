open Containers
open Bos

module StringSet = Set.Make (String)

type stats = {
  (* sisyphus runtime in seconds *)
  runtime: string;
  num_admits: int;
}

let count_admits ~test_dir ~output_name =
  let count_substring str sub =
    let sub_len = String.length sub in
    let len_diff = (String.length str) - sub_len
    and reg = Str.regexp_string sub in
    let rec aux i n =
      if i > len_diff then n else
        try
          let pos = Str.search_forward reg str i in
          aux (pos + sub_len) (succ n)
        with Not_found -> n
    in
    aux 0 0 in
  let output_path = Fpath.add_seg test_dir output_name in
  let proof_str = IO.with_in (Fpath.to_string output_path) IO.read_all in
  let count = count_substring proof_str "admit." in
  count

let parse_file path =
  let stats = IO.with_in (Fpath.to_string path) IO.read_lines_l
            |> List.map (String.split_on_char ':')
            |> List.map (List.map String.trim)
            |> List.filter_map (function [hd; tl] -> Some (hd, tl) | _ -> None)
            |> Hashtbl.of_list in
  stats

let write_to_csv ~table_dir ~headers file_stats =
  let to_row (name, stats) =
    List.map (fun key -> Hashtbl.find_opt stats key |> Option.value ~default:"") headers
    |> List.cons name
    |> String.concat ","
  in

  let headers_str = "name" :: headers |> String.concat "," in
  let row_str =
    List.to_iter file_stats
    |> Iter.map to_row
    |> Iter.intersperse "\n"
    |> Iter.concat_str in

  let stats_csv = headers_str ^ "\n" ^ row_str in

  OS.File.write Fpath.(table_dir / "stats.csv") (stats_csv)

let build_common ~table_dir common_path common_coq_lib_name =
  let open Result in
  OS.Dir.with_current table_dir (fun () ->
      let common_base_name = Fpath.basename common_path in
      let coq_dep_cmd = Cmd.(Gen_utils.coqdep
                             % "-sort"
                             % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                             % common_base_name) in
      let err =
        if Gen_utils.is_verbose_coq_mode
        then Some OS.Cmd.err_stderr
        else Some OS.Cmd.err_null in

      let* deps, _ = OS.Cmd.run_out ?err coq_dep_cmd |> OS.Cmd.out_string in
      let deps = String.split_on_char ' ' deps |> List.filter (Fun.negate String.is_empty) in

      let* _ =
        Result.fold_l (fun () dep ->
              let coqc_cmd = Cmd.(Gen_utils.coqc
                                  % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                                  % dep) in
              OS.Cmd.run ?err coqc_cmd
          ) () deps in
      Ok ()
    ) ()
  |> Result.flat_map Fun.id

(* [run_table] builds all common files, assuming they are in ../resources/Common, runs tests, and dumps proof scripts and metadata in the directory set by SIS_TABLE_DIR *)
let run_table table_dir common_path common_coq_name (tests: Gen_utils.test_config list) =
  let open Result in

  (* create table folder *)
  let* table_dir = Fpath.of_string table_dir in
  let* _ = OS.Dir.create table_dir in

  (* create common folder *)
  let common_dir = Fpath.add_seg table_dir (Fpath.basename common_path) in
  let* _ = OS.Dir.create common_dir in

  (* copy common files *)
  let common_deps = Gen_utils.copy_dep_files ~common_dir common_path in

  (* build common folder *)
  let* () = build_common ~table_dir common_path common_coq_name in

  let stats : (string, stats) Hashtbl.t = Hashtbl.create 14 in
  let files : (string, Fpath.t) Hashtbl.t = Hashtbl.create 14 in

  List.iter (fun ({ name; path; coq_name; common_path =  _; _ } : Gen_utils.test_config) -> (
        let open Gen_utils in
        Format.printf "Running %s@." name;

        let* path = Fpath.of_string path  in
        let test_dir = Fpath.add_seg table_dir (Fpath.basename path) in
        let* _ = OS.Dir.create test_dir in

        let* (deps, old_program, new_program, old_proof_name, output_name, stub_file_name) =
          build_init ~working_dir:table_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~deps:common_deps in

        (* export stats file *)
        let stats_file_name = Format.sprintf "%s_stats.txt" name in
        let stats_file = Fpath.add_seg table_dir stats_file_name in

        let start_time = Ptime_clock.now () in
        let* _ = OS.Env.set_var "SIS_STATS_OUT_FILE" Cmd.(Some (p stats_file)) in
        let* _ = run_sisyphus ~test_dir ~coq_name ~common_dir ~common_coq_name ~deps ~old_program ~new_program ~old_proof_name ~stub_file_name ~output_name in
        let end_time = Ptime_clock.now () in
        let runtime = Ptime.diff end_time start_time |>  Ptime.Span.to_float_s |> Format.sprintf "%f"  in

        (* _CoqProject file *)

        let* _ = build_res ~working_dir:table_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~output_name in

        let num_admits = count_admits ~test_dir ~output_name in

        Hashtbl.add stats name { runtime; num_admits };
        Hashtbl.add files name stats_file;

        Ok ()
      ) |> Result.get_exn) tests;

  let file_stats = Hashtbl.map_list (fun name path ->
      let file_stats = parse_file path in
      let global_stats = Hashtbl.find stats name in
      Hashtbl.add file_stats "runtime" global_stats.runtime;
      (name, file_stats)
    ) files in

  let headers =
    List.to_iter file_stats
    |> Iter.map snd
    |> Iter.flat_map Hashtbl.keys
    |> Iter.fold (Fun.flip StringSet.add) StringSet.empty
    |> StringSet.to_list
  in

  let* () = write_to_csv ~table_dir ~headers file_stats in

  Ok ()

let () =

  let usage_msg = "table -dir=<table_dir>" in
  let table_dir = ref "" in
  let speclist = [("-dir", Arg.Set_string table_dir, "Set output directory")] in
  Arg.parse speclist (fun _ -> ()) usage_msg;
  Format.printf "Arg %s" !table_dir;

  (* cd into build *)
  let  build_dir = Fpath.of_string "./_build/default/benchmarks/table" |> Result.get_exn in
  let _ =  OS.Dir.set_current build_dir |> Result.get_exn in

  (* assume common directory is same for all programs *)
  let common_path = "../../resources/common" in
  let common_path = Fpath.of_string common_path |> Result.get_exn in
  let common_coq_lib_name = "Common" in

  let tests = Test_list.test_list in
  Format.printf "NUM_TESTS = %s\n" (string_of_int @@ List.length tests);

  run_table !table_dir common_path common_coq_lib_name tests |> Result.get_exn
