open Containers
open Bos

type stats = {
  (* sisyphus runtime in seconds *)
  runtime: string;
  num_admits: int;
}

let count_admits ~test_dir ~output_name =
  let output_path = Fpath.add_seg test_dir output_name in
  let proof_str = IO.with_in (Fpath.to_string output_path)  IO.read_all in
  Format.printf "PROOF SCRIPT %s\n" proof_str;
  0

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

  List.iter (fun ({ name; path; coq_name; common_path =  _; _ } : Gen_utils.test_config) -> (
      let open Gen_utils in
      Format.printf "Running %s@." name;

      let* path = Fpath.of_string path  in
      let test_dir = Fpath.add_seg table_dir (Fpath.basename path) in
      let* _ = OS.Dir.create test_dir in


      let* (deps, old_program, new_program, old_proof_name, output_name, stub_file_name) =
        build_init ~working_dir:table_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~deps:common_deps in

      let start_time = Ptime_clock.now () in
      let* _ = run_sisyphus ~test_dir ~coq_name ~common_dir ~common_coq_name ~deps ~old_program ~new_program ~old_proof_name ~stub_file_name ~output_name in
      let end_time = Ptime_clock.now () in
      let runtime = Ptime.diff end_time start_time |> Format.sprintf "%a" Ptime.Span.pp in

      let* _ = build_res ~working_dir:table_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~output_name in

      let num_admits = count_admits ~test_dir ~output_name in

      Hashtbl.add stats name { runtime; num_admits };

      Ok ()
    ) |> Result.get_exn) tests;

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

  let tests = List.take 1 tests in

  run_table !table_dir common_path common_coq_lib_name tests |> Result.get_exn
