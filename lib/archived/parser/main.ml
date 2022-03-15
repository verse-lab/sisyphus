[@@@warning "-8-9-26-27-39"]
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
  let str = 
    begin
      try
        IO.with_in "../../resources/seq_to_array/updated.ml" Program_parser.parse_channel
      with
      | Stdlib.Parsing.Parse_error -> failwith "fail"
    end in
  print_endline @@ "function body are " ^ [%derive.show: Program.Statements.func list] str;
    ()
