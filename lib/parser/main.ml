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
        IO.with_in "../../resources/seq_to_array/updated.ml" Program_parser.raw_parse_channel
      with
      | Stdlib.Parsing.Parse_error -> failwith "fail"
    end in
  match str with
  | [{pstr_desc=Pstr_value (Nonrecursive, [{ pvb_pat={ppat_desc=Ppat_var {txt=fn_name}}; pvb_expr=body; }])}] ->
    let (args, body) = Program_parser.collect_parameters body in
    let args = List.map Program_parser.convert_pat args in
    let body = Program_parser.convert_statement body in
    print_endline @@ "function name is " ^ fn_name;
    print_endline @@ "function args are " ^ [%derive.show: Program.Statements.pattern list] args;
    print_endline @@ "function body are " ^ [%derive.show: Program.Statements.t list] body;
    ()
