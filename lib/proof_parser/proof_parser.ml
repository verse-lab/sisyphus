module Raw_parser = Raw_parser
module Proof = Proof
module Lexer = Lexer
module Parser = Parser
module Command = Command

let parse = Parser.parse
let parse_str = Parser.parse_str
let parse_channel = Parser.parse_channel
