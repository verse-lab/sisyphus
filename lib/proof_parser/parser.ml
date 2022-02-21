let parse lexbuf =
  let token () =
    let token = Lexer.token lexbuf in
    let start_,end_ = Sedlexing.lexing_positions lexbuf in
    token, start_, end_ in
  MenhirLib.Convert.Simplified.traditional2revised Raw_parser.proof  token 

let parse_str str =
  parse (Sedlexing.Utf8.from_string str)
