module PP = PPrint
let (!) = PP.string

type 'a stmt = [
  | `LetExp of Expr.typed_param * 'a Expr.simple_shape * 'a stmt
  | `LetLambda of string * [ `Lambda of Expr.typed_param list * 'a stmt ] * 'a stmt
  | `Match of 'a Expr.simple_shape * (string * (string * Type.t) list * 'a stmt) list
  | `Write of string * string * 'a Expr.simple_shape * 'a stmt
  | `Value of 'a Expr.simple_shape
  | `EmptyArray
]


type 'a lambda = [ `Lambda of Expr.typed_param list * 'a stmt ]

type 'a t = {
  converters: (string * string) list;
  prelude: string;
  name: string;
  args: (string * Type.t) list;
  body: 'a stmt
}


let rec print_stmt print_expr : 'a stmt -> _ =
  let open PP in function
  | `LetExp (param, exp, rest) ->
    group (group (! "let" ^/^ Expr.print_typed_param param ^/^ !"=") ^^ nest 2 (break 1 ^^ print_expr exp) ^/^ !"in") ^^ break 1 ^^
    group  (print_stmt print_expr rest)
  | `LetLambda (param, lambda, rest) ->
    group (group (! "let" ^/^ string param ^/^ !"=") ^/^
           nest 2 (print_lambda print_expr lambda) ^/^ !"in") ^^ break 1 ^^
    group (print_stmt print_expr rest)
  | `Match (exp, cases) ->
    group (string "match" ^/^ align (print_expr exp) ^/^ string "with") ^/^
    group (align (separate_map hardline (print_case print_expr) cases))
  | `Write (into, offset, vl, rest) ->
    group (string into ^^ string "." ^^ parens (string offset) ^/^ string "<-" ^/^ align (print_expr vl) ^^ string ";" ) ^/^
    group (align (print_stmt print_expr rest))
  | `EmptyArray -> string "[| |]"
  | `Value v -> group (print_expr v)

and print_lambda print_expr (`Lambda (params, body)) =
  let open PP in
  parens (string "fun" ^/^
   group (flow_map (break 1) Expr.print_typed_param params) ^/^ string "->" ^/^
   nest 2 (print_stmt print_expr body))  
and print_case print_expr : (string * (string * Type.t) list * 'a stmt) -> PP.document =
  let open PP in
  let param (v,ty) = parens (group (string v ^^ string ":" ^/^ Type.print ty)) in
  function
  |  (cons, [], body) ->
    group (string "|" ^/^ string cons ^/^  string "->" ^/^
           group (nest 2 (print_stmt print_expr body)))
  | ("::", [h;t], body) ->
    group (nest 4 (group (string "|" ^/^ group (group (param h ^/^ string "::" ^/^ param t) ^/^ string "->"))) ^^
          nest 2 (break 1 ^^ group (print_stmt print_expr body)))

  | (cons, args, body) ->
    group (nest 4 (group (string "|" ^/^
           group (group (parens(string cons) ^/^ (parens (group (flow_map (string "," ^^ break 1) param args)))) ^/^ string "->"))) ^^
          nest 2 (break 1 ^^ group (print_stmt print_expr body)))

let pp_lambda print_expr fmt vl = PPrint.ToFormatter.pretty 0.9 80 fmt (print_lambda print_expr vl) 
let show_lambda print_expr vl = Containers.Format.to_string (pp_lambda print_expr) vl

let pp_stmt print_expr fmt vl = PPrint.ToFormatter.pretty 0.9 80 fmt (print_stmt print_expr vl) 
let show_stmt print_expr vl = Containers.Format.to_string (pp_stmt print_expr) vl

let print print_expr t =
  let open PP in
  let param (v,ty) = parens (group (string v ^^ string ":" ^/^ Type.print ty)) in
  group (
    group (
      ! "let" ^/^ ! (t.name) ^/^ align (group (flow_map (break 1) param t.args)) ^/^ ! "=")  ^^
    nest 2 (break 1 ^^ (align @@ group (print_stmt print_expr t.body)))
  )

let pp f fmt vl =
  PPrint.ToFormatter.pretty 0.9 80 fmt (print f vl)
let show f vl = Containers.Format.to_string (pp f) vl
