[@@@warning "-8"]
open Containers

type position = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
}  [@@deriving show]

type loc = Warnings.loc = {
  loc_start : position;
  loc_end : position;
  loc_ghost : bool;
} [@@deriving show]


let () =
  begin
    try
      let str, comments = IO.with_in "../../resources/seq_to_array/updated.ml" Program_parser.parse_channel in
      print_endline @@ Pprintast.string_of_structure str;
      print_endline @@ [%derive.show: (string * loc) list] comments
    with
    | Stdlib.Parsing.Parse_error -> print_endline @@ "fail"
  end;
