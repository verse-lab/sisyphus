open Containers

let () =
  let infile = ref None in

  Arg.parse [("-infile", String (fun s -> infile := (Some s)), "ML file to print")]
    ((fun s -> infile := (Some s)))
    "Parse and print ML files using Sisyphus' internal parser engine";

  let infile = Option.get_exn_or "example directory must be given." !infile in

  let old_path = Format.sprintf "../../resources/%s/%s_old.ml" infile infile in
  let new_path = Format.sprintf "../../resources/%s/%s_new.ml" infile infile in

  let prog =
    IO.with_in old_path  IO.read_all
    |> Lang.Sanitizer.parse_str in
  Format.printf "OLD:\n%a\n" (Lang.Program.pp Lang.Expr.print) prog;

  let prog =
    IO.with_in new_path IO.read_all
    |> Lang.Sanitizer.parse_str in
  Format.printf "NEW:\n%a\n" (Lang.Program.pp Lang.Expr.print) prog
