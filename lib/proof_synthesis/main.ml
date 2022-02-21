[@@@warning "-8-9-11-26-27-39"]

open Containers


let () =
  let program = IO.with_in "../../resources/seq_to_array/updated.ml" Program_parser.parse_channel in
  print_endline @@ [%derive.show: Program.Statements.func list] program;
  ()
