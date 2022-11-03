open Containers
open Bos

let sisyphus = Cmd.v "../../bin/main.exe"
let coqdep = Cmd.v "coqdep"
let coqc = Cmd.v "coqc"
let copy = Cmd.v "cp"

let is_verbose_coq_mode =
  OS.Env.var "SIS_VERBOSE_COQ_BENCHMARK"
  |> Option.flat_map Int.of_string
  |> Option.value ~default:0 > 0

let is_cached_build_mode =
  OS.Env.var "SIS_FAST_BENCHMARK"
  |> Option.flat_map Int.of_string
  |> Option.value ~default:0 > 0

let is_table_mode =
  OS.Env.var "SIS_TABLE_MODE"
  |> Option.flat_map Int.of_string
  |> Option.value ~default:0 > 0

let is_ml_file path =
  let basename = Fpath.basename path in
  Fpath.has_ext ".ml" path && not (String.suffix ~suf:"sisyphus.ml" basename)

let copy_dep_files ~common_dir path =
  let open Result in
  let common_cfml_output_path = Fpath.(path / "_output") in

  let deps = ref [] in

  let res = OS.Dir.fold_contents (fun path acc ->
    let* () = acc in

    let base_name = Fpath.basename path in

    let in_output = Fpath.is_prefix common_cfml_output_path path in
    let valid_file =
      Fpath.has_ext ".v" path ||
      (Fpath.has_ext ".ml" path &&
       not (String.suffix ~suf:"sisyphus.ml" base_name)) ||
      (Fpath.has_ext ".vo" path && is_cached_build_mode) in
    if valid_file && not in_output
    then begin
      Format.printf "%a ==> %s@." Fpath.pp path base_name;
      if is_ml_file path then deps := Fpath.(common_dir / base_name) :: !deps;
      OS.Cmd.run Cmd.(copy % "--no-preserve=mode,ownership" % "-v" % p path % p Fpath.(common_dir /  base_name))
    end
    else
      Ok ()
  ) (Ok ()) path in
  match res with
  | Ok _ -> !deps
  | Error `Msg m ->
    Format.ksprintf ~f:failwith
      "failed to initialise setup directory with error: %s" m

let build_coq_project ~working_dir path coq_lib_name common_path common_coq_lib_name =
  let open Result in
  OS.Dir.with_current working_dir (fun () -> (
      let base_name = Fpath.basename path in
      let common_base_name = Fpath.basename common_path in

      let coq_dep_cmd = Cmd.(coqdep
                             % "-sort"
                             % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                             % "-R" % ("./" ^ base_name) % coq_lib_name
                             % base_name
                             % common_base_name) in

      let err =
        if is_verbose_coq_mode
        then Some OS.Cmd.err_stderr
        else Some OS.Cmd.err_null in

      let* deps, _ = OS.Cmd.run_out ?err coq_dep_cmd |> OS.Cmd.out_string in
      let deps = String.split_on_char ' ' deps |> List.filter (Fun.negate String.is_empty) in
      let* _ =
        Result.fold_l Result.(fun () dep ->
          let* dep_path = (Fpath.of_string (dep ^ "o")) in
          let* exists = OS.Path.exists dep_path in
          Format.printf "dep path exists %a ==> %b@." Fpath.pp dep_path exists;
          if exists && (is_cached_build_mode || is_table_mode) then Ok ()
          else
            let coqc_cmd = Cmd.(coqc
                                % "-R" % ("./" ^ common_base_name) % common_coq_lib_name
                                % "-R" % ("./" ^ base_name) % coq_lib_name
                                % dep) in
            OS.Cmd.run ?err coqc_cmd
        ) () deps in
      Ok ()
    )) ()
  |> Result.flat_map Fun.id

let run_sisyphus ~test_dir ~coq_name ~common_dir ~common_coq_name ~deps ~old_program ~new_program ~old_proof_name ~stub_file_name ~output_name =
  let open Result in
  let* _ =
    let sisyphus_cmd =
      let binary =
        List.fold_left
          (fun b ml_file -> Cmd.(b % "--dep" % p ml_file))
          sisyphus deps in
      let binary =
        Cmd.(binary % "-c" % (Format.sprintf "%s:%a" common_coq_name Fpath.pp common_dir)) in
      Cmd.(binary % p old_program % p new_program
           % p test_dir % coq_name
           % old_proof_name % stub_file_name % output_name) in

    let err = OS.Cmd.err_stderr in
    OS.Cmd.run ~err sisyphus_cmd
    |> Result.map_err (fun (`Msg err) -> `Msg ("Running Sisyphus failed with error: " ^ err)) in
  Ok ()

let build_res ~working_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~output_name =
  let open Result in
  let* () =
    OS.Dir.with_current working_dir (fun () ->
        let base_name = Fpath.basename path in
        let common_base_name = Fpath.basename common_path in

        let coq_dep_cmd = Cmd.(coqc
                               % "-R" % ("./" ^ common_base_name) % common_coq_name
                               % "-R" % ("./" ^ base_name) % coq_name
                               % p Fpath.(test_dir / output_name)) in

        OS.Cmd.run coq_dep_cmd
      ) () |> Result.flat_map Fun.id
    |> Result.map_err (fun (`Msg err) -> `Msg ("Output from sisyphus failed to build with error: " ^ err)) in
  Ok ()

let build_init ~working_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~deps =
  let open Result in
  let old_program, new_program, old_proof, new_proof, deps = ref None, ref None, ref None, ref None, ref deps in
  let cfml_output_path = Fpath.(path / "_output") in

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
    ) (Ok ()) path in

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
  let* () = build_coq_project ~working_dir path coq_name common_path common_coq_name
            |> Result.map_err (fun (`Msg err) -> `Msg ("Initial project failed to build with error: " ^ err)) in

  Ok (deps, old_program, new_program, old_proof_name, output_name, stub_file_name)

let run_full_test ~working_dir ~test_dir ~common_dir ~path ~coq_name ~common_path ~common_coq_name ~deps =
  let open Result in

  let* (deps, old_program, new_program, old_proof_name, output_name, stub_file_name) =
    build_init ~working_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~deps in

  let* () = run_sisyphus ~test_dir ~coq_name ~common_dir ~common_coq_name ~deps ~old_program ~new_program ~old_proof_name ~stub_file_name ~output_name in

  let* () = build_res ~working_dir ~test_dir ~path ~coq_name ~common_path ~common_coq_name ~output_name in
  Ok ()

type test_config = {
  name: string;
  path: string;
  coq_name: string;
  common_path: string;
  common_coq_name: string;
} [@@deriving show]

let test_list : test_config list ref = ref []

let add_test name ~path ~coq_name ~common_path ~common_coq_name =
  test_list := { name; path; coq_name; common_path; common_coq_name } :: !test_list

let get_test_list () = !test_list
