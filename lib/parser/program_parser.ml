

let parse lexbuf =
  let result = Parser.implementation Lexer.token lexbuf in
  let comments = Lexer.comments () in
  result, comments
let parse_str str = parse (Lexing.from_string ~with_positions:true str)
let parse_channel chan = parse (Lexing.from_channel ~with_positions:true chan)

