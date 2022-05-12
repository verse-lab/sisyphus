open Containers

let rec pp_ty fmt (ty: Lang.Type.t) =
  match ty with
  | Lang.Type.Unit -> Format.fprintf fmt "unit"
  | Lang.Type.Var var -> Format.fprintf fmt "%s"  (String.drop 1 (String.uppercase_ascii var))
  | Lang.Type.Int -> Format.fprintf fmt "int" 
  | Lang.Type.Func -> Format.fprintf fmt "func"
  | Lang.Type.Loc -> Format.fprintf fmt "loc"
  | Lang.Type.List ty -> Format.fprintf fmt "list (%a)" pp_ty ty
  | Lang.Type.Array ty -> Format.fprintf fmt "array (%a)" pp_ty ty
  | Lang.Type.Ref ty -> Format.fprintf fmt "ref (%a)" pp_ty ty
  | Lang.Type.Product tys ->
    List.pp
      ~pp_start:(fun fmt () -> Format.fprintf fmt "(")
      ~pp_stop:(fun fmt () -> Format.fprintf fmt ")")
      ~pp_sep:(fun fmt () -> Format.fprintf fmt " * ") pp_ty
      fmt tys
  | Lang.Type.ADT (name, args, _) ->
    Format.fprintf fmt "(%s %a)"
      name (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
           (fun fmt exp -> Format.fprintf fmt "(%a)" pp_ty exp)) args

let rec pp_expr fmt (expr: Lang.Expr.t) =
  match expr with
  | `Var s -> Format.fprintf fmt "%s" s
  | `Tuple args ->
    List.pp
      ~pp_start:(fun fmt () -> Format.fprintf fmt "(")
      ~pp_stop:(fun fmt () -> Format.fprintf fmt ")")
      ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_expr
      fmt args
  | `App ("+", [l;r]) ->
    Format.fprintf fmt "(%a + %a)"
      pp_expr l pp_expr r
  | `App ("-", [l;r]) ->
    Format.fprintf fmt "(%a - %a)"
      pp_expr l pp_expr r
  | `App (f, args) ->
    Format.fprintf fmt "(%s %a)"
      f (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_expr)
      args
  | `Lambda (params, body) ->
    Format.fprintf fmt "(fun %a => %a)"
      (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") pp_typed_param)
      params pp_expr body
  | `Int n -> Format.fprintf fmt "%d" n
  | `Constructor ("[]", []) -> Format.fprintf fmt "nil"
  | `Constructor ("::", [h; t]) ->
    Format.fprintf fmt "%a :: %a" pp_expr h pp_expr t
  | `Constructor (f, args) ->
    Format.fprintf fmt "%s(%a)"
      f (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp_expr) args
and pp_typed_param fmt (param: Lang.Expr.typed_param) =
  match param with
  | `Var (var, ty) ->
    Format.fprintf fmt "(%s: %a)" var pp_ty ty
  | `Tuple params ->
    let params, tys = List.split params in
    Format.fprintf fmt "'(%a: %a)"
      (List.pp
         ~pp_start:(fun fmt () -> Format.fprintf fmt "(")
         ~pp_stop:(fun fmt () -> Format.fprintf fmt ")")
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         Format.pp_print_string) params
      pp_ty (Lang.Type.Product tys)

let rec pp_stmt fmt (stmt: Lang.Expr.t Lang.Program.stmt) =
  match stmt with
  | `LetExp (param, _, exp, rest) ->
    Format.fprintf fmt "let %a := %a in %a"
      pp_typed_param param
      pp_expr exp
      pp_stmt rest
  | `LetLambda (name, exp, rest) -> 
    Format.fprintf fmt "let %s := %a in %a"
      name
      pp_lambda exp
      pp_stmt rest
  | `Value expr -> pp_expr fmt expr
  | `Match (on_exp, cases) ->
    Format.fprintf fmt "match %a with %a end"
      pp_expr on_exp
      (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
         (fun fmt (cons_name, params, rest) ->
            Format.fprintf fmt "| %s %a => %a"
              cons_name
              (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
                 (fun fmt (name, ty) -> Format.fprintf fmt "(%s: %a)" name pp_ty ty)) params
              pp_stmt rest
         )) cases
  | `EmptyArray
  | `Write _ -> failwith "attempted to print a mutable expression as a gallina term." 
and pp_lambda fmt (`Lambda (args, body): [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) =
  Format.fprintf fmt "(fun %a => %a)"
    (List.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt " ") pp_typed_param) args
    pp_stmt body

let show_expr = Format.to_string pp_expr
let show_ty = Format.to_string pp_ty
let show_stmt = Format.to_string pp_stmt
let show_lambda = Format.to_string pp_lambda
