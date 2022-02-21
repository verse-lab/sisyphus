[@@@warning "-8-9-11-26-27-39"]
open Containers

let comments = ref []
let no_comments_to_ignore = ref 0 

let parse_raw lexbuf =
  comments := [];
  let result = Parser.implementation Lexer.token lexbuf in
  comments := List.drop (!no_comments_to_ignore) @@ Lexer.comments ();
  no_comments_to_ignore := !no_comments_to_ignore + List.length !comments;
  result
let parse_raw_expr lexbuf =
  comments := [];
  let result = Parser.parse_expression Lexer.token lexbuf in
  comments := List.drop (!no_comments_to_ignore) @@  Lexer.comments ();
  no_comments_to_ignore := !no_comments_to_ignore + List.length !comments;
  result

let raw_parse_expr str = parse_raw_expr (Lexing.from_string ~with_positions:true str)
let raw_parse_str str = parse_raw (Lexing.from_string ~with_positions:true str)
let raw_parse_channel chan = parse_raw (Lexing.from_channel ~with_positions:true chan)


let rec convert_pat (pat: Parsetree.pattern) : Program.Statements.pattern =
  match pat with
  | { ppat_desc=Ppat_var {txt;_}; ppat_loc; ppat_loc_stack; ppat_attributes } ->
    Var txt
  | {ppat_desc=Ppat_tuple pats} -> Tuple (List.map convert_pat pats)
  | {ppat_desc=Ppat_construct ({txt=Lident name}, None)} -> Constructor (name, [])
  | {ppat_desc=Ppat_construct ({txt=Lident name}, Some {ppat_desc=Ppat_tuple pats})} ->
    let pats = List.map convert_pat pats in
    Constructor (name, pats)
  | {ppat_desc=Ppat_any} -> Wildcard
  | pat -> failwith @@ "unsupported pattern: " ^ Format.to_string Pprintast.pattern pat

let collect_parameters (expr: Parsetree.expression) : (Parsetree.pattern list * Parsetree.expression) =
  let rec loop acc (expr: Parsetree.expression) = 
    match expr with
    | { pexp_desc=Pexp_fun (_, _, pat, exp) } ->
      loop (pat :: acc) exp
    | expr -> (List.rev acc, expr)
  in
  loop [] expr

let convert_comparison_op op l r : Program.Expr.bool_expr = match op, l,r with
  | "<", l, r -> Lt (l,r)
  | ">", l, r -> Gt (l,r)
  | "<=", l, r -> Le (l,r)
  | ">=", l, r -> Ge (l, r)

let rec convert_pure_expression (expr: Parsetree.expression) : Program.Expr.expr =
  match expr with
  | { pexp_desc = Pexp_constant (Pconst_integer (i, _)); pexp_loc; pexp_loc_stack; pexp_attributes } ->
    IntExpr (Int (Int.of_string_exn i))
  | { pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident "+"}}, [Nolabel, l;Nolabel, r]) } ->
    let l = convert_pure_expression l |> Program.Expr.unwrap_int_expr in
    let r = convert_pure_expression r |> Program.Expr.unwrap_int_expr in
    IntExpr (Add (l,r))
  | { pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident "-"}}, [Nolabel, l;Nolabel, r]) } ->
    let l = convert_pure_expression l |> Program.Expr.unwrap_int_expr in
    let r = convert_pure_expression r |> Program.Expr.unwrap_int_expr in
    IntExpr (Sub (l,r))
  | { pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident (("<" | ">" | ">=" | "<=") as op)}}, [Nolabel, l;Nolabel, r]) } ->
    let l = convert_pure_expression l |> Program.Expr.unwrap_int_expr in
    let r = convert_pure_expression r |> Program.Expr.unwrap_int_expr in
    BoolExpr (convert_comparison_op op l r)
  | { pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident "="}}, [Nolabel, l;Nolabel, r]) } -> begin
      match convert_pure_expression l, convert_pure_expression r with
      | IntExpr l, r -> let r = Program.Expr.unwrap_int_expr r in BoolExpr (IntEq (l, r))
      | l, IntExpr r -> let l = Program.Expr.unwrap_int_expr l in BoolExpr (IntEq (l, r))
      | ListExpr l, r -> let r = Program.Expr.unwrap_list_expr r in BoolExpr (ListEq (l, r))
      | l, ListExpr r -> let l = Program.Expr.unwrap_list_expr l in BoolExpr (ListEq (l, r))
    end
  | {pexp_desc=Pexp_construct ({txt=Lident "true"}, None)} -> BoolExpr (Bool true)
  | {pexp_desc=Pexp_construct ({txt=Lident "false"}, None)} -> BoolExpr (Bool false)
  | {pexp_desc=Pexp_construct ({txt=Lident "[]"}, None)} -> ListExpr Nil
  | {pexp_desc=Pexp_construct ({txt=Lident "::"}, Some ({pexp_desc=Pexp_tuple ([h;t])}))} ->
    let h = convert_pure_expression h  in
    let t = convert_pure_expression t |> Program.Expr.unwrap_list_expr in
    ListExpr (AppList ("cons", [h; ListExpr t]))
  | {pexp_desc = Pexp_ident {txt=Lident v}} -> Var v
  | {pexp_desc=Pexp_tuple exprs} -> TupleExpr (List.map convert_pure_expression exprs)
  | _ -> failwith @@ "unable to support: " ^ Format.to_string Pprintast.expression expr

let rec convert_slc (expr: Parsetree.expression) : Program.Statements.slc list =
  match expr with
  | {pexp_desc=Pexp_sequence (l,r)} ->
    let l = convert_slc l in
    let r = convert_slc r in
    l @ r
  | {pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Ldot (Lident "Array", "set")}},
                           [Nolabel, {pexp_desc=Pexp_ident {txt=Lident arr}};
                            Nolabel, ind;
                            Nolabel, vl])} as exp ->
    let ind = convert_pure_expression ind in
    let vl = convert_pure_expression vl in
    [`ArrayAssign (arr, ind, vl)]
  | exp ->
    let exp = convert_pure_expression exp in
    [`Expr exp]

let retrieve_comments_before (expr: Parsetree.expression) =
  let next_comment () : (string * Warnings.loc) option  = match !comments with
    | [] -> None
    | h :: t -> Some h in
  let pop_comment () = match !comments with
    | [] -> ()
    | _ :: t -> comments := t in

  let (<) (l: Lexing.position) (r: Lexing.position) : bool =
    (l.pos_lnum < r.pos_lnum) || (l.pos_lnum = r.pos_lnum && l.pos_bol < r.pos_bol) in
    
  let expr_start = expr.pexp_loc.loc_start in
  let rec loop acc =
    match next_comment () with
    | Some (comment, { loc_end }) when loc_end < expr_start ->
      pop_comment ();
      loop ((`Comment comment) :: acc)
    | _ -> List.rev acc in

  loop []

let rec convert_statement (expr: Parsetree.expression) : Program.Statements.t list =
  let comments = retrieve_comments_before expr in
  comments @ 
  match expr with
  | {pexp_desc=Pexp_sequence (l,r)} ->
    let l = convert_statement l in
    let r = convert_statement r in
    l @ r
  | {pexp_desc = Pexp_array []} -> [`EmpArray]
  | { pexp_desc=Pexp_match ({pexp_desc=Pexp_ident {txt=Lident var}}, cases) } ->
    [`MatchPure (var, List.map convert_case cases)]
  | { pexp_desc=Pexp_match ({pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Lident var}},
                                                   [Nolabel, {pexp_desc=Pexp_construct ({txt=Lident "()"}, _)}])},
                            cases) } ->
    [`MatchDeferred (var, List.map convert_case cases)]
  | {pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=Lident "iteri"})}, [
    Nolabel, {pexp_desc=Pexp_fun (Nolabel, None, {ppat_desc=Ppat_var {txt=ind_var}},
                                  {pexp_desc=Pexp_fun (Nolabel, None, {ppat_desc=Ppat_var {txt=elt_var}}, body) }) };
    Nolabel, ls;
  ])} ->
    let body = convert_slc body in
    let ls = convert_pure_expression ls in
    [`Iteri (ind_var, elt_var, body, ls)]
  | {pexp_desc=
       Pexp_let (Nonrecursive,
                 [{pvb_pat={ppat_desc=Ppat_var {txt=out_var}};
                   pvb_expr={pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=Lident "length'"})}, [
                    Nolabel, ls;
                  ])}}], rest)} ->
    let ls = convert_pure_expression ls in
    let rest = convert_statement rest in
    (`Length (out_var, ls)) :: rest
  | {pexp_desc=
       Pexp_let (Nonrecursive,
                 [{pvb_pat; pvb_expr={pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=Lident "fold"})}, [
                    Nolabel, {pexp_desc=Pexp_fun (Nolabel, None, acc_pat,
                                                  {pexp_desc=Pexp_fun (Nolabel, None, {ppat_desc=Ppat_var {txt=elt}}, body) }) };
                    Nolabel, init;
                    Nolabel, ls;
                  ])}}], rest)} ->
    let out_pat = convert_pat pvb_pat in
    let acc_pat = convert_pat acc_pat in
    let vl_pat = elt in
    let body = convert_slc body in
    let init = convert_pure_expression init in
    let ls = convert_pure_expression ls in
    let rest = convert_statement rest in
    (`Fold (out_pat, acc_pat, vl_pat, body, init, ls)) :: rest
  | {pexp_desc=
       Pexp_let (Nonrecursive,
                 [{pvb_pat; pvb_expr={pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=Ldot (Lident "List", "fold_left")})}, [
                    Nolabel, {pexp_desc=Pexp_fun (Nolabel, None, acc_pat,
                                                  {pexp_desc=Pexp_fun (Nolabel, None, {ppat_desc=Ppat_var {txt=elt}}, body) }) };
                    Nolabel, init;
                    Nolabel, ls;
                  ])}}], rest)} ->
    let out_pat = convert_pat pvb_pat in
    let acc_pat = convert_pat acc_pat in
    let vl_pat = elt in
    let body = convert_slc body in
    let init = convert_pure_expression init in
    let ls = convert_pure_expression ls in
    let rest = convert_statement rest in
    (`ListFold (out_pat, acc_pat, vl_pat, body, init, ls)) :: rest
  | {pexp_desc=
       Pexp_let (Nonrecursive,
                 [{pvb_pat={ppat_desc=Ppat_var {txt=var}};
                   pvb_expr={pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=Ldot (Lident "Array", "make")})}, [
                    Nolabel, len;
                    Nolabel, {pexp_desc=Pexp_ident {txt=Lident vl}};
                  ])}}], rest)} ->
    let len = convert_pure_expression len in
    let rest = convert_statement rest in
    (`AllocArray (var, len, vl)) :: rest
  | {pexp_desc=Pexp_let (Nonrecursive, [{pvb_pat={ppat_desc=Ppat_var {txt}}; pvb_expr=exp}], rest) } ->
    let exp = convert_pure_expression exp in
    let rest = convert_statement rest in
    (`LetPure (txt, exp)) :: rest
  | exp -> (convert_slc exp :> Program.Statements.t list)

and convert_case ({pc_lhs; pc_rhs}: Parsetree.case) : (Program.Statements.pattern * Program.Statements.t list) =
  convert_pat pc_lhs, convert_statement pc_rhs

let convert_declaration : Parsetree.structure_item -> Program.Statements.func = function
  | {pstr_desc=Pstr_value (Nonrecursive, [{ pvb_pat={ppat_desc=Ppat_var {txt=fn_name}}; pvb_expr=body; }])} ->
    let (args, body) = collect_parameters body in
    let args = List.map convert_pat args in
    let body = convert_statement body in
    (fn_name, args, body)


let parse str = List.map convert_declaration (raw_parse_str str)
let parse_channel chan = List.map convert_declaration (raw_parse_channel chan)
