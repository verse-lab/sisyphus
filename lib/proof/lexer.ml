open Containers
module P = Raw_parser

let identstart = [%sedlex.regexp? 'A'..'Z'
                              | 'a'..'z'
                              | '_' | '\192'..'\214'
                              | '\216'..'\246'
                              |'\248'..'\255' | '@' ]
let identbody = [%sedlex.regexp? 'A'..'Z'
                             | 'a'..'z'
                             | '0' .. '9'
                             |'_' | '\192'..'\214'
                             |'\216'..'\246'
                             |'\248'..'\255'
                             |'\'']
let ident = [%sedlex.regexp? identstart, Star identbody]
let digit = [%sedlex.regexp? Plus ('0' .. '9') ]
let not_full_stop = [%sedlex.regexp? Star (Compl '.')]
let not_semi_or_full_stop_or_paren_or_sqbrace = [%sedlex.regexp? Star (Compl (';' |'.' | '(' | ')' | '[' | ']'))]
let not_paren_or_sqbrace = [%sedlex.regexp? Star (Compl ('(' | ')' | '[' | ']' | '.'))]
let not_lbrace_or_rbrace = [%sedlex.regexp? Star (Compl ('{' |'}'))]
let whitespace = [%sedlex.regexp? Plus (' ' | '\013' | '\009' | '\012')]
let skip_whitespace = [%sedlex.regexp? Star (' ' | '\013' | '\009' | '\012')]

type ustr = Uchar.t array 
let ustr_to_str str =
  Array.to_seq str |> Seq.map Uchar.to_char |> String.of_seq
let lexeme lexbuf = ustr_to_str (Sedlexing.lexeme lexbuf)

let rec token lexbuf =
  match%sedlex lexbuf with
  | whitespace -> token lexbuf
  | '\010' -> Sedlexing.new_line lexbuf; token lexbuf
  | "." -> P.FULL_STOP
  | "Set", whitespace -> set_flag lexbuf
  | "From", whitespace -> require_import_library lexbuf
  | "Lemma" -> P.LEMMA
  | "," -> P.COMMA
  | "-" -> P.PROOF_DASH_OR_SUB
  | digit -> P.INT (Int.of_string_exn @@ lexeme lexbuf)
  | "case_eq", whitespace -> case_eq lexbuf
  | "SPEC" -> P.SPEC
  | "PRE" -> P.PRE
  | "POST" -> P.POST
  | "xcf" -> P.XCF
  | "xpull" -> P.XPULL
  | "xapp" -> P.XAPP
  | "xmatch" -> P.XMATCH
  | "xlet" -> P.XLET
  | "xvals" -> P.XVALS
  | "xseq" -> P.XSEQ
  | "++" -> P.APPEND
  | "+" -> P.ADD
  | "{" ->
    let buf = Buffer.create 1024 in
    Buffer.add_char buf '{';
    opaque_coq_script buf 0 lexbuf
  | ";", skip_whitespace ->
    let buf = Buffer.create 1024 in
    semi_with_coq_proof buf lexbuf
  | "\\[" -> P.PURE_LBRACE
  | "[" -> P.LSQBRACE
  | "]" -> P.RSQBRACE
  | "fun" -> P.FUN
  | "=>" -> P.ARROW
  | "~>" -> P.PTS
  | "(" -> P.LPAREN | ")" -> P.RPAREN
  | ":" -> P.COLON
  | "forall" -> P.FORALL
  | "`{" -> P.IMPLICIT_LBRACE | "}" -> P.IMPLICIT_RBRACE
  | "Proof using" -> P.PROOF_USING
  | "Qed" -> P.QED
  | ident ->
    let ident = lexeme lexbuf in
    let ident = if String.prefix ~pre:"@" ident then String.drop 1 ident else ident in
    P.IDENT ident
  | _ -> P.EOF
and set_flag lexbuf =
  match%sedlex lexbuf with
  | not_full_stop -> P.DIRECTIVE (Command.SetFlag (lexeme lexbuf))
  | _ -> failwith "invalid input 70"
and require_import_library =
  let rec require_import_library_from library lexbuf =
    match%sedlex lexbuf with
    | whitespace -> require_import_library_from library lexbuf
    | "Require", whitespace, "Import", whitespace ->
      require_import_library_from_modules library lexbuf
    | _ -> failwith "invalid input 77"
  and require_import_library_from_modules library lexbuf =
    match%sedlex lexbuf with
    | whitespace -> require_import_library_from_modules library lexbuf
    | not_full_stop ->
      let libs = String.split_on_char ' ' (lexeme lexbuf) in
      P.DIRECTIVE (Command.ImportFrom (library, libs))
    | _ -> failwith "invalid input 84"
  in
  fun lexbuf ->
  match%sedlex lexbuf with
  | whitespace -> require_import_library lexbuf 
  | ident ->
    let library = lexeme lexbuf in
    require_import_library_from library lexbuf
  | _ -> failwith "invalid input 92"
and semi_with_coq_proof buf lexbuf =
  match%sedlex lexbuf with
  | not_semi_or_full_stop_or_paren_or_sqbrace, ('[' | '(') ->
    Buffer.add_string buf (lexeme lexbuf);
    semi_with_coq_proof_inside_braces buf 1 lexbuf
  | not_semi_or_full_stop_or_paren_or_sqbrace ->
    Buffer.add_string buf (lexeme lexbuf);
    P.SEMI_WITH_COQ_PROOF (Buffer.contents buf)
  | _ -> failwith "invalid input"
and semi_with_coq_proof_inside_braces buf depth lexbuf =
  match%sedlex lexbuf with
  | not_semi_or_full_stop_or_paren_or_sqbrace, ('[' | '(') ->
    Buffer.add_string buf (lexeme lexbuf);
    semi_with_coq_proof_inside_braces buf (depth + 1) lexbuf
  | not_semi_or_full_stop_or_paren_or_sqbrace, (']' | ')') ->
    Buffer.add_string buf (lexeme lexbuf);
    if depth <= 0
    then P.SEMI_WITH_COQ_PROOF (Buffer.contents buf)
    else if depth > 1
    then semi_with_coq_proof_inside_braces buf (depth - 1) lexbuf
    else semi_with_coq_proof buf lexbuf
  | not_paren_or_sqbrace ->
    Buffer.add_string buf (lexeme lexbuf);
    if depth <= 0
    then P.SEMI_WITH_COQ_PROOF (Buffer.contents buf)
    else semi_with_coq_proof_inside_braces buf depth lexbuf
  | _ -> failwith "invalid input"

and case_eq lexbuf =
  let rec case_eq_cases var lexbuf =
    match%sedlex lexbuf with
    | whitespace -> case_eq_cases var lexbuf
    | skip_whitespace, ";", skip_whitespace,
      "[", Star (skip_whitespace, "intros", skip_whitespace,  Plus (skip_whitespace, ident), skip_whitespace, "|"),
                 skip_whitespace, "intros", skip_whitespace,  Plus (skip_whitespace, ident), skip_whitespace,
      "]" ->
      let intro_pats = lexeme lexbuf |> String.trim |> String.drop 1 |> String.trim in
      let intro_pats = String.sub intro_pats 1 (String.length intro_pats - 2) in
      let cases = String.split_on_char '|' intro_pats
                  |> List.map String.trim
                  |> List.map (String.drop (String.length "intros"))
                  |> List.map String.trim
                  |> List.map (String.split_on_char ' ')
                  |> List.map (List.map String.trim) in
      P.CASE_EQ (var, cases)
    | "[", any, "]" -> failwith @@ "invalid input 124: "^ lexeme lexbuf 
    | _ -> failwith @@ "invalid input 124: "^ lexeme lexbuf in
  match%sedlex lexbuf with
  | whitespace -> case_eq lexbuf 
  | ident ->
    let var = lexeme lexbuf in
    case_eq_cases var lexbuf
  | _ -> failwith "invalid input 130"
and opaque_coq_script buf depth lexbuf =
  match%sedlex lexbuf with
  | '}' ->
    Buffer.add_char buf '}';
    if depth <= 0
    then P.COQ_PROOF (Buffer.contents buf)
    else opaque_coq_script buf (depth - 1)  lexbuf
  | '{' ->
    Buffer.add_char buf '}';
    opaque_coq_script buf (depth + 1) lexbuf
  | not_lbrace_or_rbrace ->
    Buffer.add_string buf (lexeme lexbuf);
    opaque_coq_script buf depth lexbuf
  | _ -> failwith "invalid input 144"
