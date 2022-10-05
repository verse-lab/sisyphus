open Containers
open Bos

let sisyphus = Cmd.v "../../bin/main.exe"
let coqdep = Cmd.v "coqdep"
let coqc = Cmd.v "coqc"
let copy = Cmd.v "cp"

let is_debug_mode =
  let env_vars =
    OS.Env.var "OCAMLRUNPARAM"
    |> Option.map (String.split_on_char ',')
    |> Option.value ~default:[]
    |> List.map (String.trim)
    |> List.filter String.is_empty in
  List.mem "b" env_vars

let build_coq_project ~temp_dir path coq_lib_name common_path common_coq_lib_name =
  let open Result in
  OS.Dir.with_current temp_dir (fun () -> (
        let base_name = Fpath.basename path in
        let common_base_name = Fpath.basename common_path in

        let coq_dep_cmd = Cmd.(coqdep
                               % "-sort"
                               % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                               % "-R" % ("./" ^ base_name) % coq_lib_name
                               % base_name
                               % common_base_name) in

        let err =
          if is_debug_mode
          then Some OS.Cmd.err_stderr
          else Some OS.Cmd.err_null in

        let* deps, _ = OS.Cmd.run_out ?err coq_dep_cmd |> OS.Cmd.out_string in
        let deps = String.split_on_char ' ' deps |> List.filter (Fun.negate String.is_empty) in
        let* _ =
          Result.fold_l (fun () dep ->
              let coqc_cmd = Cmd.(coqc
                                  % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                                  % "-R" % ("./" ^ base_name) % coq_lib_name
                                  % dep) in
              OS.Cmd.run ?err coqc_cmd
            ) () deps in
        Ok ()
      )) ()
  |> Result.flat_map Fun.id

let run_sisyphus path coq_lib_name common_path common_coq_lib_name =
  let open Result in
  let (basename : string) = Fpath.basename path in

  (* create a temp directory with 2 sub-dirs: common_dir and test_dir *)
  let* temp_dir = OS.Dir.tmp ("sisyphus_test_" ^^ (Scanf.format_from_string basename "") ^^ "_%s") in

  let common_dir = Fpath.add_seg temp_dir (Fpath.basename common_path) in
  let* _ = OS.Dir.create common_dir in

  let test_dir = Fpath.add_seg temp_dir basename in
  let* _ = OS.Dir.create test_dir in


  let old_program, new_program, old_proof, new_proof, deps = ref None, ref None, ref None, ref None, ref [] in
  let cfml_output_path = Fpath.(path / "_output") in

  let is_ml_file path =
    let basename = Fpath.basename path in
    Fpath.has_ext ".ml" path && not (String.suffix ~suf:"sisyphus.ml" basename)
  in


  (* setup test directory *)
  let copy_dep_files path : unit =
    let common_cfml_output_path = Fpath.(path / "_output") in

    let _ = OS.Dir.fold_contents (fun path acc ->
        let* () = acc in

        (* let* curr = OS.Dir.current () in *)
        (* Format.printf "Current dir: %a @." Fpath.pp curr; *)
        let base_name = Fpath.basename path in
        (* Format.printf "%a @." Fpath.pp path; *)
        let in_output = Fpath.is_prefix common_cfml_output_path path in
        let valid_file =
          Fpath.has_ext ".v" path ||
          (Fpath.has_ext ".ml" path &&
           not (String.suffix ~suf:"sisyphus.ml" base_name)) in
        if valid_file && not in_output
        then begin
          Format.printf "%a ==> %s@." Fpath.pp path base_name;
          if is_ml_file path then deps := Fpath.(common_dir / base_name) :: !deps;
          OS.Cmd.run Cmd.(copy % p path %  p Fpath.(common_dir /  base_name))
        end
        else
          Ok ()
      ) (Ok ()) path
    in
    ()
  in

  copy_dep_files common_path;

  let* _ =
    OS.Dir.fold_contents (fun path acc ->
        let* () = acc in
        let base_name = Fpath.basename path in
        let in_output = Fpath.is_prefix cfml_output_path path in
        let valid_file =
          (Fpath.has_ext ".v" path) ||
          (Fpath.has_ext ".ml" path &&
           not (String.suffix ~suf:"sisyphus.ml" base_name))
        in
        let is_new_proof = String.suffix ~suf:"_new.v" base_name in
        if valid_file && not in_output
        then begin
          Format.printf "%a ==> %s@." Fpath.pp path (Fpath.basename path);
          (* extract old program, new program, old proof, new proof_stub *)
          begin match () with
            | _ when String.suffix ~suf:"_old.ml" base_name -> old_program := Some Fpath.(test_dir / base_name)
            | _ when String.suffix ~suf:"_new.ml" base_name -> new_program := Some Fpath.(test_dir / base_name)
            | _  when String.suffix ~suf:"_old.v" base_name -> old_proof   := Some Fpath.(test_dir / base_name)
            | _ when String.suffix ~suf:"_new.v" base_name ->  new_proof   := Some path
            (* temporary ml files are generated with the suffix <filename>.sisyphus.ml, so these should be ignored when testing. *)
            | _ when Fpath.has_ext ".ml" path && not (String.suffix ~suf:"sisyphus.ml" base_name) ->
              deps := Fpath.(test_dir / base_name) :: !deps
            | _ -> ()
          end;

          (* copy over the files *)
          if not is_new_proof
          then  OS.Cmd.run Cmd.(copy % p path %  p Fpath.(test_dir / base_name))
          else Ok ()
        end
        else Ok ()
      ) (Ok ()) path
  in

  let deps = !deps in
  let old_program = Option.get_exn_or "" !old_program in
  let new_program = (Option.get_exn_or "" !new_program) in
  let old_proof_name = Fpath.basename (Option.get_exn_or "" !old_proof) in
  let new_proof = (Option.get_exn_or "" !new_proof) in
  let output_name = Fpath.basename new_proof in

  (* setup stub input *)
  let stub_file_name = Fpath.basename new_proof ^ "_stub" in

  let* () =
    let* new_file_contents = OS.File.read new_proof in
    let end_index = String.find ~sub:"Proof using (All)." new_file_contents in
    assert (end_index > 0);
    let stub = String.sub new_file_contents 0 (end_index + (String.length "Proof using (All).")) in
    print_endline stub;
    OS.File.write Fpath.(test_dir / stub_file_name) stub in

  (* build coq project *)
  let* () = build_coq_project ~temp_dir path coq_lib_name common_path common_coq_lib_name
            |> Result.map_err (fun (`Msg err) -> `Msg ("Initial project failed to build with error: " ^ err)) in

  (*  run sisyphus *)
  let* _ =
    let sisyphus_cmd =
      let binary =
        List.fold_left
          (fun b ml_file -> Cmd.(b % "--dep" % p ml_file))
          sisyphus deps in
      let binary =
        Cmd.(binary % "-c" % (Format.sprintf "%s:%a" common_coq_lib_name Fpath.pp common_dir)) in
      Cmd.(binary % p old_program % p new_program
           % p test_dir % coq_lib_name
           % old_proof_name % stub_file_name % output_name) in

    let err = OS.Cmd.err_stderr in
    OS.Cmd.run_out ~err sisyphus_cmd |> OS.Cmd.out_string
              |> Result.map_err (fun (`Msg err) -> `Msg ("Running Sisyphus failed with error: " ^ err)) in

  (* build result file *)
  let* () =
    OS.Dir.with_current temp_dir (fun () ->
        let base_name = Fpath.basename path in
        let common_base_name = Fpath.basename common_path in

        let coq_dep_cmd = Cmd.(coqc
                               % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                               % "-R" % ("./" ^ base_name) % coq_lib_name
                               % p Fpath.(test_dir / output_name)) in

        OS.Cmd.run coq_dep_cmd
      ) () |> Result.flat_map Fun.id
    |> Result.map_err (fun (`Msg err) -> `Msg ("Output from sisyphus failed to build with error: " ^ err)) in

  Ok ()

let result =
  Alcotest.testable
    (Result.pp'
       (fun fmt () -> Format.pp_print_string fmt "()")
       (fun fmt (`Msg m) -> Format.fprintf fmt "`Msg %s" m))
    Equal.poly

let sisyphus_runs_on ~path ~coq_name ~common_path ~common_coq_name () =
  let path = Fpath.of_string path |> Result.get_exn in
  let common_path = Fpath.of_string common_path |> Result.get_exn in
  Alcotest.check result (Format.sprintf "Sisyphus builds project") (Ok ()) (run_sisyphus path coq_name common_path common_coq_name)

let tests = ref []

let run name =
  Alcotest.run name
    (List.map (fun f -> f ()) @@ List.rev !tests)

module Make (S: sig val name: string end) = struct

  let module_tests = ref [];;

  tests := (fun () -> S.name, List.rev !module_tests) :: !tests

  let add_test name test =
    module_tests := (name, `Quick, test) :: !module_tests

  let add_slow_test name test =
    module_tests := (name, `Slow, test) :: !module_tests

  let run () = run S.name

end
