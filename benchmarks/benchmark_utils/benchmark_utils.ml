open Containers
open Bos


let run_sisyphus path coq_lib_name common_path common_coq_lib_name =
  let open Result in
  let (basename : string) = Fpath.basename path in

  (* create a temp directory with 2 sub-dirs: common_dir and test_dir *)
  let* temp_dir = OS.Dir.tmp ("sisyphus_test_" ^^ (Scanf.format_from_string basename "") ^^ "_%s") in

  let common_dir = Fpath.add_seg temp_dir (Fpath.basename common_path) in
  let* _ = OS.Dir.create common_dir in

  let test_dir = Fpath.add_seg temp_dir basename in
  let* _ = OS.Dir.create test_dir in

  let common_deps = Gen_utils.copy_dep_files ~common_dir common_path in

  let* _ = Gen_utils.run_test ~working_dir:temp_dir ~test_dir ~common_dir ~path ~coq_lib_name ~common_path common_coq_lib_name common_deps in

  Ok ()


let result =
  Alcotest.testable
    (Result.pp'
       (fun fmt () -> Format.pp_print_string fmt "()")
       (fun fmt (`Msg m) -> Format.fprintf fmt "`Msg %s" m))
    Equal.poly


let test_config = ref ("", "", "", "")

let sisyphus_runs_on ~path ~coq_name ~common_path ~common_coq_name =
  if Gen_utils.is_table_mode then
    test_config := (path, coq_name, common_path, common_coq_name);


  fun () ->
  let path = Fpath.of_string path |> Result.get_exn in
  let common_path = Fpath.of_string common_path |> Result.get_exn in
  Format.printf "%a \n %a \n" Fpath.pp path Fpath.pp common_path;
  Alcotest.check result (Format.sprintf "Sisyphus builds project") (Ok ()) (run_sisyphus path coq_name common_path common_coq_name)


let tests = ref []
let h = Hashtbl.create 10

let run name =
  if not Gen_utils.is_table_mode
  then
  Alcotest.run ~verbose:true name
    (List.map (fun f -> f ()) @@ List.rev !tests)
  else
      Format.printf "%s\n" name;

module Make (S: sig val name: string end) = struct

  let module_tests = ref [];;

  tests := (fun () -> S.name, List.rev !module_tests) :: !tests

  let add_test name test =
    module_tests := (name, `Quick, test) :: !module_tests;
    Hashtbl.add h name !test_config

  let add_slow_test name test =
    module_tests := (name, `Slow, test) :: !module_tests

  let run () = run S.name
end
