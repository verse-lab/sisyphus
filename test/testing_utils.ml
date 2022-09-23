open Containers
open Bos

let sisyphus = Cmd.v "../bin/main.exe"
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

let build_coq_project ~coq_lib_name test_dir =
  let open Result in
  (* build coq project *)
  OS.Dir.with_current test_dir (fun () ->
    let* contents = OS.Dir.contents test_dir in
    let coq_dep_cmd =
      List.fold_left (fun b file ->
        if Fpath.has_ext ".v" file
        then Cmd.(b % p file)
        else b)
        Cmd.(coqdep % "-sort" % "-R" % "./" % coq_lib_name) contents in
    let err =
      if is_debug_mode
      then Some OS.Cmd.err_stderr
      else Some OS.Cmd.err_null in
    let* deps, _ = OS.Cmd.run_out ?err coq_dep_cmd |> OS.Cmd.out_string in
    let deps = String.split_on_char ' ' deps |> List.filter (Fun.negate String.is_empty) in
    let* () =
      Result.fold_l (fun () dep ->
        OS.Cmd.run ?err Cmd.(coqc % "-R" % "./" % coq_lib_name % dep)
      ) () deps in
    Ok ()
  ) () |> Result.flat_map Fun.id

let run_sisyphus path coq_lib_name =
  let open Result in
  let basename = Fpath.basename path in
  (* create a temp directory *)
  let* test_dir = OS.Dir.tmp ("sisyphus_test_" ^^ (Scanf.format_from_string basename "") ^^ "_%s") in

  let old_program, new_program, old_proof, new_proof, deps = ref None, ref None, ref None, ref None, ref [] in
  let cfml_output_path = Fpath.(path / "_output") in
  (* setup test directory *)
  let* _ =
    OS.Dir.fold_contents (fun path acc ->
      let* () = acc in
      let base_name = Fpath.basename path in
      let in_output = Fpath.is_prefix cfml_output_path path in
      let valid_file =
        Fpath.has_ext ".v" path ||
        (Fpath.has_ext ".ml" path &&
         not (String.suffix ~suf:"sisyphus.ml" base_name)) in
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
        OS.Cmd.run Cmd.(copy % p path %  p Fpath.(test_dir / base_name))
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
  let* () = build_coq_project ~coq_lib_name test_dir
    |> Result.map_err (fun (`Msg err) -> `Msg ("Initial project failed to build with error: " ^ err)) in

  (*  run sisyphus *)
  let* () =
    let sisyphus_cmd =
      let binary =
        List.fold_left
          (fun b ml_file -> Cmd.(b % "--dep" % p ml_file))
          sisyphus deps in
      Cmd.(binary % p old_program % p new_program
           % p test_dir % coq_lib_name
           % old_proof_name % stub_file_name % output_name) in
    OS.Cmd.run sisyphus_cmd
    |> Result.map_err (fun (`Msg err) -> `Msg ("Running Sisyphus failed with error: " ^ err)) in

  (* build result file *)
  let* () =
    OS.Dir.with_current test_dir (fun () ->
      OS.Cmd.run Cmd.(coqc  % "-R" % "./" % coq_lib_name % output_name)
    ) () |> Result.flat_map Fun.id
    |> Result.map_err (fun (`Msg err) -> `Msg ("Output from sisyphus failed to build with error: " ^ err)) in

  Ok ()

let result =
  Alcotest.testable
    (Result.pp'
       (fun fmt () -> Format.pp_print_string fmt "()")
       (fun fmt (`Msg m) -> Format.fprintf fmt "`Msg %s" m))
    Equal.poly

let sisyphus_runs_on ~path ~coq_name () =
  let path = Fpath.of_string path |> Result.get_exn in
  Alcotest.check result (Format.sprintf "Sisyphus builds project") (run_sisyphus path coq_name) (Ok ())

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
