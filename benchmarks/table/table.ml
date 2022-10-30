open Containers
open Bos
module Tests = Tests

let table_dir =
  OS.Env.var "SIS_TABLE_DIR"
  |> Option.value ~default:""

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


let result =
  Alcotest.testable
    (Result.pp'
       (fun fmt () -> Format.pp_print_string fmt "()")
       (fun fmt (`Msg m) -> Format.fprintf fmt "`Msg %s" m))
    Equal.poly

(* [run_table] builds all common files, assuming they are in ../resources/Common, runs tests, and dumps proof scripts and metadata in the directory set by SIS_TABLE_DIR *)
let run_table common_path common_coq_lib_name tests =
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
  let* () = build_common ~table_dir common_path common_coq_lib_name in

  List.iter (fun (name, (path, coq_lib_name, _, _)) ->
      let path = Fpath.of_string path |> Result.get_exn in
      let test_dir = Fpath.add_seg table_dir (Fpath.basename path) in
      let _ = OS.Dir.create test_dir|> Result.get_exn in
      Alcotest.check result (Format.sprintf "Sisyphus builds project %s" name) (Ok ()) (Gen_utils.run_test ~working_dir:table_dir ~test_dir ~common_dir ~path ~coq_lib_name ~common_path common_coq_lib_name common_deps)
    ) tests;

  Ok ()

let () =
  let open Result in
  let common_path = "../../resources/common" in
  let common_path = Fpath.of_string common_path |> Result.get_exn in
  let common_coq_lib_name = "Common" in

  let tests = Benchmark_utils.h
            |> Hashtbl.to_seq
            |> Seq.to_list in

  Alcotest.check result (Format.sprintf "Sisyphus builds project") (Ok ()) (run_table common_path common_coq_lib_name tests)
