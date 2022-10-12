module PP = PPrint
let (!) = PP.string

type 'a stmt = [
  | `LetExp of Expr.typed_param * string option * 'a Expr.simple_shape * 'a stmt
  | `LetLambda of string * [ `Lambda of Expr.typed_param list * 'a stmt ] * 'a stmt
  | `Match of 'a Expr.simple_shape * (string * (string * Type.t) list * 'a stmt) list
  | `Write of string * string * 'a Expr.simple_shape * 'a stmt
  | `AssignRef of string * 'a Expr.simple_shape * 'a stmt
  | `Value of 'a Expr.simple_shape
  | `IfThenElse of 'a Expr.simple_shape * 'a stmt * 'a stmt
  | `IfThen of 'a Expr.simple_shape * 'a stmt * 'a stmt
  | `EmptyArray
] [@@deriving show, eq][@@end]
let ppr_stmt = pp_stmt
let showr_stmt = show_stmt


type 'a lambda = [ `Lambda of Expr.typed_param list * 'a stmt ]
[@@deriving show]
let ppr_lambda = pp_lambda
let showr_lambda = show_lambda

type structure_item = Parsetree.structure_item
let pp_structure_item fmt vl = Pprintast.structure fmt [vl]

type 'a t = {
  prelude: structure_item list;
  logical_mappings: (string * string) list;
  name: string;
  args: (string * Type.t) list;
  body: 'a stmt
}
[@@deriving show]
let ppr = pp
let showr = show

let equal eq t1 t2 =
  String.equal t1.name t2.name
  && List.equal (fun (l,r) (l', r') -> String.equal l l' && String.equal r r') t1.logical_mappings t2.logical_mappings
  && List.equal (fun (l,r) (l', r') -> String.equal l l' && Type.equal r r') t1.args t2.args
  && equal_stmt eq t1.body t2.body

let lookup_statement (id: Id.t) prog =
  let rec loop pos (body: 'a stmt) =
    match body with
    | _ as v when pos = id -> Ok v
    | `EmptyArray | `Value _ -> Error (Id.incr pos)
    | `Write (_, _, _, rest) -> loop (Id.incr pos) rest
    | `AssignRef (_, _, rest) -> loop (Id.incr pos) rest
    | `LetExp (_, _, _, rest) -> loop (Id.incr pos) rest
    | `LetLambda (_, `Lambda (_, lambody), rest) ->
      begin match loop pos lambody with
      | Ok v -> Ok v
      | Error pos -> loop pos rest
      end
    | `IfThenElse (_, l, r) ->
      begin match loop (Id.incr pos) l with
      | Ok v -> Ok v
      | Error pos -> loop (Id.incr pos) r
      end
    | `IfThen (_, l, r) ->
      begin match loop (Id.incr pos) l with
      | Ok v -> Ok v
      | Error pos -> loop (Id.incr pos) r
      end
    | `Match (_, cases) ->
      let rec fold pos (cases: (string * (string * Type.t) list * 'a stmt) list) =
        match cases with
        | [] -> Error pos
        | (_, _, h) :: t -> match loop pos h with
          | Ok v -> Ok v
          | Error pos -> fold pos t in
      fold (Id.incr pos) cases in
  loop Id.init prog.body
  |> Result.to_option


let rec print_stmt print_expr : 'a stmt -> _ =
  let open PP in function
  | `LetExp (param, _, exp, rest) ->
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
  | `AssignRef (into, vl, rest) ->
    group (string into ^/^ string ":=" ^/^ align (print_expr vl) ^^ string ";" ) ^/^
    group (align (print_stmt print_expr rest))

  | `IfThenElse (cond, l, r) ->
    group (group (string "if" ^/^ print_expr cond)  ^/^
           group (string "then" ^/^ print_stmt print_expr l) ^/^
           group (string "else" ^/^ print_stmt print_expr r))
  | `IfThen (cond, l, r) ->
    group (group (group (string "if" ^/^ print_expr cond)  ^/^
                  group (string "then" ^/^ print_stmt print_expr l)) ^^ string ";"  ^/^ 
           print_stmt print_expr r)
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

let print_stmt_line print_expr : 'a stmt -> _ =
  let open PP in function
  | `LetExp (param, _, exp, _) ->
    group (group (! "let" ^/^ Expr.print_typed_param param ^/^ !"=") ^^ nest 2 (break 1 ^^ print_expr exp) ^/^ !"in")
  | `LetLambda (param, lambda, _) ->
    group (group (! "let" ^/^ string param ^/^ !"=") ^/^
           nest 2 (print_lambda print_expr lambda) ^/^ !"in") 
  | `Match (exp, _) ->
    group (string "match" ^/^ align (print_expr exp) ^/^ string "with")
  | `Write (into, offset, vl, _) ->
    group (string into ^^ string "." ^^ parens (string offset) ^/^ string "<-" ^/^ align (print_expr vl) ^^ string ";" )
  | `AssignRef (into, vl, _) ->
    group (string into ^/^ string ":=" ^/^  align (print_expr vl) ^^ string ";" )
  | `IfThenElse (cond, _, _) ->
    group (string "if" ^/^ print_expr cond ^/^ string "then" ^/^ string "..." ^/^ string "else"  ^/^ string "...")
  | `IfThen (cond, _, _) ->
    group (string "if" ^/^ print_expr cond ^/^ string "then" ^/^ string "...")
  | `EmptyArray -> string "[| |]"
  | `Value v -> group (print_expr v)


let pp_lambda print_expr fmt vl = PPrint.ToFormatter.pretty 0.9 80 fmt (print_lambda print_expr vl) 
let show_lambda print_expr vl = Containers.Format.to_string (pp_lambda print_expr) vl

let pp_stmt print_expr fmt vl = PPrint.ToFormatter.pretty 0.9 80 fmt (print_stmt print_expr vl) 
let show_stmt print_expr vl = Containers.Format.to_string (pp_stmt print_expr) vl

let pp_stmt_line print_expr fmt vl = PPrint.ToFormatter.pretty 0.9 80 fmt (print_stmt_line print_expr vl) 
let show_stmt_line print_expr vl = Containers.Format.to_string (pp_stmt_line print_expr) vl


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
