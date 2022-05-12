
[@@@warning "-8-9-11-26-27-39"]
open Containers
module StringSet = Set.Make (String)

let parse_raw lexbuf =
  let result = Parser.implementation Lexer.token lexbuf in
  result
let parse_raw_expr lexbuf =
  let result = Parser.parse_expression Lexer.token lexbuf in
  result

let raw_parse_expr_str str = parse_raw_expr (Lexing.from_string ~with_positions:true str)
let raw_parse_expr_channel chan = parse_raw_expr (Lexing.from_channel ~with_positions:true chan)
let raw_parse_str str = parse_raw (Lexing.from_string ~with_positions:true str)
let raw_parse_channel chan = parse_raw (Lexing.from_channel ~with_positions:true chan)

let lident (ident: Longident.t) =
  match ident with
  | Longident.Lident id -> id
  | _ -> Format.sprintf "%a" Pprintast.longident ident

let rec convert_typ (ty: Parsetree.core_type) : Type.t =
  match ty.ptyp_desc with
  | Parsetree.Ptyp_var v -> Var ("'" ^ v)
  | Parsetree.Ptyp_arrow (_, _, _) -> Func
  | Parsetree.Ptyp_tuple tys -> Product (List.map convert_typ tys)
  | Parsetree.Ptyp_constr ({txt=Lident "list"}, [ty]) ->
    List (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "array"}, [ty]) ->
    Array (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "ref"}, [ty]) ->
    Ref (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "int"}, []) ->
    Int
  | Parsetree.Ptyp_constr ({txt=Lident user}, ity) ->
    let conv =
      List.find_map (fun (attr: Parsetree.attribute) ->
        match attr.attr_name.txt, attr.attr_payload with
        | "collection", PStr [{pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident {txt=lident; _}; _}, _); _}] ->
          Some (Longident.flatten lident |> String.concat ".")
        | _ ->
          None
      ) ty.ptyp_attributes
       (* TODO: this is a hack to get around limitation of CFML that
          adding annotations cause crashes. As such, we assume
          Common.of_list will always be the conversion function *)
      |> Option.or_ ~else_:(Some ("Common.of_list"))
    in
    ADT (user, List.map convert_typ ity, conv)
  | Ptyp_poly (_, ty) -> convert_typ ty
  | _ ->
    failwith @@ Format.sprintf "unsupported type %a"
                  Pprintast.core_type ty

let rec convert_pat (pat: Parsetree.pattern) : Expr.typed_param =
  match pat with
  | { ppat_desc=Ppat_constraint ({ppat_desc=Ppat_var {txt;_}}, ty);  } ->
    `Var (txt, convert_typ ty)
  | {ppat_desc=Ppat_tuple pats} ->
    `Tuple (List.map
              (fun Parsetree.{
                 ppat_desc=Ppat_constraint ({ppat_desc=Ppat_var {txt;_}}, ty)} ->
                 (txt, convert_typ ty)
              ) pats)
  | {ppat_desc=Ppat_any} -> `Var ("unused", Unit)
  | pat -> failwith (Format.sprintf "unsupported pattern %a" Pprintast.pattern pat)

let add_pat_args set = function
  | `Var (t, _) -> StringSet.add t set
  | `Tuple args -> List.fold_left (fun set (v, _) -> StringSet.add v set) set args

let rec convert_expr (expr: Parsetree.expression) : Expr.t =
  match expr with
  | { pexp_desc=Pexp_ident ({txt=Lident var}) } -> `Var var
  | {pexp_desc=Pexp_constant (Pconst_integer (i, _)) } -> `Int (Int.of_string_exn i)
  | {pexp_desc=Pexp_tuple ts}  -> `Tuple (List.map convert_expr ts)
  | {pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident ({txt=fn})}, args)} ->
    let fn = lident fn in
    let args = List.map (fun (Asttypes.Nolabel, expr) -> convert_expr expr) args in
    `App (fn, args)
  | {pexp_desc=Pexp_construct ({txt=Lident cons}, Some {pexp_desc=Pexp_tuple ts})} ->
    let ts = List.map convert_expr ts in
    `Constructor (cons, ts)
  | {pexp_desc=Pexp_construct ({txt=Lident cons}, None)} ->
    `Constructor (cons, [])
  | {pexp_desc=Pexp_construct ({txt=Lident cons}, Some e)} ->
    `Constructor (cons, [convert_expr e])
  | {pexp_desc=Pexp_fun (_, _, _, _)} as e ->
    let rec collect_params acc : Parsetree.expression -> _ = function
      | {pexp_desc=Pexp_fun (_, _, pat, body)} ->
        collect_params (convert_pat pat :: acc) body
      | body ->
        let body = convert_expr body in
        `Lambda (List.rev acc, body) in
    collect_params [] e
  | e -> failwith (Format.sprintf "unsupported ast %a" Pprintast.expression e)

let fresh_var ?(hint="tmp") ctx =
  let rec loop i =
    let hint = hint ^ Int.to_string i in
    if StringSet.mem hint ctx
    then loop (i + 1)
    else (hint, StringSet.add hint ctx) in
  if StringSet.mem hint ctx
  then loop 0
  else (hint, StringSet.add hint ctx)

let extract_rewrite_hint (attrs: Parsetree.attributes) =
  List.find_map (function
    | Parsetree.{ attr_name={txt="rewrite";_}; attr_payload; _ } ->
      begin
        match attr_payload with
        | Parsetree.PStr [{ pstr_desc=Pstr_eval ({pexp_desc=Pexp_ident {txt=name}; _}, _); pstr_loc }] ->
          Some (Longident.flatten name |> String.concat ".")
        |  _ -> failwith "unexpected structure for rewrite hint"
      end
    | _ -> None
  ) attrs

let rec convert_stmt (ctx: StringSet.t) (expr: Parsetree.expression) : _ Program.stmt =
  match expr with
  | {pexp_desc=Pexp_let (Nonrecursive, [{pvb_pat; pvb_expr={pexp_desc=Pexp_fun _ } as e}], rest)} ->
    let expr = convert_lambda ctx e in
    let (`Var (param, _)) : Expr.typed_param = convert_pat pvb_pat in
    let ctx = StringSet.add param ctx in
    let rest = convert_stmt ctx rest in
    `LetLambda (param, expr, rest)
  (* when we have a let of a function application *)
  | {pexp_desc=Pexp_let (Nonrecursive, [{
    pvb_pat;
    pvb_expr={
      pexp_desc=Pexp_apply ({
        pexp_desc=Pexp_ident {txt=fn}
      }, args)}}], rest)} ->
    let fn = lident fn in
    let param = convert_pat pvb_pat in
    (* extract rewrite hint from binding *)
    let rewrite_hint = extract_rewrite_hint pvb_pat.ppat_attributes in
    (* create a kont that when given arguments to lambda + rest of code, returns the structure *)
    let kont = fun (args,rest) -> `LetExp (param, rewrite_hint, `App (fn, List.rev args), rest) in
    let ctx = add_pat_args ctx param in
    (* fold through the arguments to replace higher order functions with preceding let bindings *)
    let kont, ctx = List.fold_left (fun (kont, ctx) ->
      function
      (* if argument is a function *)
      | (Asttypes.Nolabel, (Parsetree.{pexp_desc=Pexp_fun _ } as e)) ->
        let lambda = convert_lambda ctx e in
        let param, ctx =  fresh_var ctx in
        (* update kontinuation to be preceded by a let lambda binding *)
        let kont = (fun (args, rest) ->
          `LetLambda (param, lambda, kont (`Var param :: args, rest))
        ) in
        (kont, ctx)
      (* otherwise,  *)
      | (Asttypes.Nolabel, e) ->
        let e = convert_expr e in
        let kont = (fun (args, rest) -> kont (e :: args, rest)) in
        (kont, ctx)
    ) (kont, ctx) (List.rev args) in
    (* convert rest of code *)
    let rest = convert_stmt ctx rest in
    (* finally, call constructed continuation *)
    kont ([], rest)
  | {pexp_desc=Pexp_let (Nonrecursive, [{pvb_pat; pvb_expr}], rest)} ->
    let param = convert_pat pvb_pat in
    let expr = convert_expr pvb_expr in
    let ctx = add_pat_args ctx param in
    let rest = convert_stmt ctx rest in
    let rewrite_hint = extract_rewrite_hint pvb_pat.ppat_attributes in
    `LetExp (param, rewrite_hint, expr, rest)
  | {pexp_desc=Pexp_match (e, cases)} ->
    let e = convert_expr e in
    let cases = List.map (convert_case ctx) cases in
    `Match (e, cases)
  | {pexp_desc=Pexp_array []} -> `EmptyArray
  | {pexp_desc=Pexp_sequence ({pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=Ldot (Lident "Array", "set")}},
                                                     Parsetree.[_, {pexp_desc=Pexp_ident {txt=Lident arr}};
                                                                _, {pexp_desc=Pexp_ident {txt=Lident i}};
                                                                _, vl])},rest)} ->
    let vl = convert_expr vl in
    let rest = convert_stmt ctx rest in
    `Write (arr, i, vl, rest)
  | e -> `Value (convert_expr e)
and convert_case ctx : Parsetree.case -> _ = function
  | {pc_lhs; pc_rhs} ->
    let cons, vars = match pc_lhs with
      | {ppat_desc=Ppat_construct ({txt=Lident cons}, Some {ppat_desc=Ppat_tuple ts})} ->
        let ts =
          List.map (fun Parsetree.{ppat_desc=Ppat_constraint ({ppat_desc=Ppat_var {txt;_}}, ty)} ->
            (txt, convert_typ ty)) ts in
        (cons, ts)
      | {ppat_desc=
           Ppat_construct (
             {txt=Lident cons},
             Some {ppat_desc=Ppat_constraint({ppat_desc=Ppat_var {txt}}, ty)})} ->
        (cons, [txt, convert_typ ty])
      | {ppat_desc=Ppat_construct ({txt=Lident cons}, None)} ->
        (cons, []) in
    let ctx = List.fold_left (fun set (v, _) -> StringSet.add v set) ctx vars in
    let body = convert_stmt ctx pc_rhs in
    cons, vars, body
and convert_lambda ctx e =
  let rec collect_params ctx acc : Parsetree.expression -> _ = function
    | {pexp_desc=Pexp_fun (_, _, pat, body)} ->
      let pat = convert_pat pat in
      let ctx = add_pat_args ctx pat in
      collect_params ctx (pat :: acc) body
    | body ->
      let body = convert_stmt ctx body in
      `Lambda (List.rev acc, body) in
  collect_params ctx [] e 

let split_last ls =
  let rec loop acc last =
    function
    | [] -> (List.rev acc, last)
    | h :: t -> loop (last :: acc) h t in
  match[@warning "-8"] ls with
  | h :: t ->
    loop [] h t

let convert : Parsetree.structure -> 'a Program.t = function
  | pats ->
    let prelude, {
      pstr_desc=Pstr_value (Nonrecursive,
                            [{pvb_pat={ppat_desc=Ppat_var {txt=name}};
                              pvb_expr}])} = split_last pats in
    (* let prelude = to_str pres in *)
    let rec collect_params acc : Parsetree.expression -> _ = function
      | {pexp_desc=
           Pexp_fun (_, _, {
             ppat_desc=Ppat_constraint ({
               ppat_desc=Ppat_var {txt}}, ty)}, body)} ->
        collect_params ((txt, convert_typ ty) :: acc) body
      | body ->
        let params = List.rev acc in
        let ctx =  List.fold_left (fun set (v, _) ->  StringSet.add v set)
                     StringSet.empty params in
        let body = convert_stmt ctx body in
        (params, body) in
    let args, body = collect_params [] pvb_expr in
    {prelude;name;args;body}

let parse_lambda_str str = raw_parse_expr_str str |> convert_lambda StringSet.empty
let parse_expr_str str = raw_parse_expr_str str |> convert_expr
let parse_str str = raw_parse_str str |> convert
