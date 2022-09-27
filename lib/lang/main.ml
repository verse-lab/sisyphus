[@@@warning "-33"]
open Containers

let () =

  let program_txt = IO.with_in "../../resources/seq_to_array/seq_to_array_new.ml" IO.read_all in

  print_endline @@ (Lang.Sanitizer.parse_raw (Lexing.from_string program_txt) |> (Format.to_string Pprintast.structure));

  let program = program_txt |> Lang.Sanitizer.parse_str in
  print_endline @@
  Lang.Program.show Lang.Expr.print program
