
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
  | Parsetree.Ptyp_arrow (_, t1, t2) ->
    Func (Some (convert_fun_ty [convert_typ t1] t2))
  | Parsetree.Ptyp_tuple tys -> Product (List.map convert_typ tys)
  | Parsetree.Ptyp_constr ({txt=Lident "list"}, [ty]) ->
    List (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "array"}, [ty]) ->
    Array (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "ref"}, [ty]) ->
    Ref (convert_typ ty)
  | Parsetree.Ptyp_constr ({txt=Lident "int"}, []) ->
    Int
  | Parsetree.Ptyp_constr ({txt=Lident "bool"}, []) ->
    Bool
  | Parsetree.Ptyp_constr ({txt=Lident "unit"}, []) ->
    Unit
  | Parsetree.Ptyp_constr ({txt=Lident user}, ity) ->
    let conv =
      List.find_map (fun (attr: Parsetree.attribute) ->
        match attr.attr_name.txt, attr.attr_payload with
        | "collection", PStr [{pstr_desc=Pstr_eval (
          {pexp_desc=Pexp_tuple [
             {pexp_desc=Pexp_ident {txt=of_list_lident; _}; _};
             {pexp_desc=Pexp_ident {txt=to_list_lident; _}; _}
           ]; _}, _); _}] ->
          let lid_to_str lident = Longident.flatten lident |> String.concat "." in
          Some (lid_to_str of_list_lident, lid_to_str to_list_lident)
        | "collection", PStr [{pstr_desc=Pstr_eval (exp, _); _}] ->
          Format.ksprintf ~f:failwith  "found unsupported payload %a" Pprintast.expression exp
        | _ -> None
      ) ty.ptyp_attributes in
    ADT (user, List.map convert_typ ity, conv)
  | Ptyp_poly (_, ty) -> convert_typ ty
  | _ ->
    failwith @@ Format.sprintf "unsupported type %a"
                  Pprintast.core_type ty
and convert_fun_ty acc (ty: Parsetree.core_type) =
  match ty.ptyp_desc with
  | Parsetree.Ptyp_arrow (_, t1, t2) ->
    convert_fun_ty (convert_typ t1 :: acc) t2
  | _ -> List.rev acc, convert_typ ty

let rec convert_pat (pat: Parsetree.pattern) : Expr.typed_param =
  match pat with
  | { ppat_desc=Ppat_constraint ({ppat_desc=Ppat_any}, ty);  } ->
    `Var ("unused", convert_typ ty)
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

let pexp_tag: Parsetree.expression_desc -> string = function
  | Parsetree.Pexp_ident _ -> "Pexp_ident" | Parsetree.Pexp_constant _ -> "Pexp_constant"
  | Parsetree.Pexp_let (_, _, _) -> "Pexp_let" | Parsetree.Pexp_function _ -> "Pexp_function"
  | Parsetree.Pexp_fun (_, _, _, _) -> "Pexp_fun" | Parsetree.Pexp_apply (_, _) -> "Pexp_apply"
  | Parsetree.Pexp_match (_, _) -> "Pexp_match" | Parsetree.Pexp_try (_, _) -> "Pexp_try"
  | Parsetree.Pexp_tuple _ -> "Pexp_tuple" | Parsetree.Pexp_construct (_, _) -> "Pexp_construct"
  | Parsetree.Pexp_variant (_, _) -> "Pexp_variant" | Parsetree.Pexp_record (_, _) -> "Pexp_record"
  | Parsetree.Pexp_field (_, _) -> "Pexp_field" | Parsetree.Pexp_setfield (_, _, _) -> "Pexp_setfield"
  | Parsetree.Pexp_array _ -> "Pexp_array" | Parsetree.Pexp_ifthenelse (_, _, _) -> "Pexp_ifthenelse"
  | Parsetree.Pexp_sequence (_, _) -> "Pexp_sequence" | Parsetree.Pexp_while (_, _) -> "Pexp_while"
  | Parsetree.Pexp_for (_, _, _, _, _) -> "Pexp_for" | Parsetree.Pexp_constraint (_, _) -> "Pexp_constraint"
  | Parsetree.Pexp_coerce (_, _, _) -> "Pexp_coerce" | Parsetree.Pexp_send (_, _) -> "Pexp_send"
  | Parsetree.Pexp_new _ -> "Pexp_new" | Parsetree.Pexp_setinstvar (_, _) -> "Pexp_setinstvar"
  | Parsetree.Pexp_override _ -> "Pexp_override" | Parsetree.Pexp_letmodule (_, _, _) -> "Pexp_letmodule"
  | Parsetree.Pexp_letexception (_, _) -> "Pexp_letexception" | Parsetree.Pexp_assert _ -> "Pexp_assert"
  | Parsetree.Pexp_lazy _ -> "Pexp_lazy" | Parsetree.Pexp_poly (_, _) -> "Pexp_poly"
  | Parsetree.Pexp_object _ -> "Pexp_object" | Parsetree.Pexp_newtype (_, _) -> "Pexp_newtype"
  | Parsetree.Pexp_pack _ -> "Pexp_pack" | Parsetree.Pexp_open (_, _) -> "Pexp_open"
  | Parsetree.Pexp_letop _ -> "Pexp_letop" | Parsetree.Pexp_extension _ -> "Pexp_extension"
  | Parsetree.Pexp_unreachable -> "Pexp_unreachable"

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
  | e -> failwith (Format.sprintf "unsupported ast %a[%s]" Pprintast.expression e (pexp_tag e.pexp_desc))

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
  | {pexp_desc=Pexp_sequence ({pexp_desc=Pexp_apply ({pexp_desc=Pexp_ident {txt=(Lident ":=")}},
                                                     Parsetree.[_, {pexp_desc=Pexp_ident {txt=Lident rf}};
                                                                _, vl])},rest)} ->
    let vl = convert_expr vl in
    let rest = convert_stmt ctx rest in
    `AssignRef (rf, vl, rest)
  | {pexp_desc=Pexp_ifthenelse (cond, l, Some r)} ->
    let cond = convert_expr cond in
    let l = convert_stmt ctx l in
    let r = convert_stmt ctx r in
    `IfThenElse (cond, l, r)
  | {pexp_desc=Pexp_sequence ({pexp_desc=Pexp_ifthenelse (cond, l, None)}, rest)} ->
    let cond = convert_expr cond in
    let l = convert_stmt ctx l in
    let rest = convert_stmt ctx rest in
    `IfThen (cond, l, rest)
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

let rec convert_list : Parsetree.expression -> Parsetree.expression list =
  function
    { pexp_desc=Pexp_construct ({txt=Lident "::";_}, Some { pexp_desc=Pexp_tuple [hd; tl]; _}) ; _ } ->
    hd :: convert_list tl
  | { pexp_desc=Pexp_construct ({txt=Lident "[]";_}, None) ; _ } ->
    []
  | expr ->
    Format.ksprintf ~f:failwith "convert_list expecting either a cons or nil constructor, but called with expression %a"
      Pprintast.expression expr

let convert_pair : Parsetree.expression -> Parsetree.expression * Parsetree.expression =
  function
    { pexp_desc=Pexp_tuple [fst;snd] ; _ } ->
    (fst,snd)
  | expr ->
    Format.ksprintf ~f:failwith "convert_pair expecting a tuple of two elements, but called with expression %a"
      Pprintast.expression expr

let convert_string_expr : Parsetree.expression -> string =
  function
    { pexp_desc=Pexp_constant (Pconst_string (s, _, _)) ; _ } -> s
  | { pexp_desc=Pexp_ident {txt=s; _}; _} ->
    (Longident.flatten s |> String.concat ".")
  | expr ->
    Format.ksprintf ~f:failwith "convert_string_const expecting a string literal, but called with expression %a"
      Pprintast.expression expr

let convert : Parsetree.structure -> 'a Program.t = function
  | pats ->
    let prelude, {
      pstr_desc=Pstr_value (Nonrecursive,
                            [{pvb_pat={ppat_desc=Ppat_var {txt=name}};
                              pvb_expr; pvb_attributes}])} = split_last pats in

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
    let logical_mappings =
      begin
        let open Option in
        let* mapping = List.find_opt (fun attr ->
          String.equal "with_logical_mapping" attr.Parsetree.attr_name.txt 
        ) pvb_attributes in
        match mapping.attr_payload with
        | Parsetree.PStr [{ pstr_desc=Pstr_eval (expr, _); pstr_loc }] ->
          let elts = convert_list expr
                     |> List.map convert_pair
                     |> List.map (Pair.map_same convert_string_expr) in
          Some elts
        | _ -> failwith "invalid structure for logical mappings"
      end |> Option.value ~default:[] in
    let opaque_encoders =
      begin
        let open Option in
        let* mapping = List.find_opt (fun attr ->
          String.equal "with_opaque_encoding" attr.Parsetree.attr_name.txt 
        ) pvb_attributes in
        match mapping.attr_payload with
        | Parsetree.PStr [{ pstr_desc=Pstr_eval (expr, _); pstr_loc }] ->
          let elts = convert_list expr
                     |> List.map convert_pair
                     |> List.map (Pair.map_snd convert_pair)
                     |> List.map (Pair.map_snd (Pair.map_same convert_string_expr))
                     |> List.map (Pair.map_fst convert_string_expr) in
          Some elts
        | _ -> failwith "invalid structure for opaque encoders mappings"
      end |> Option.value ~default:[] in


    {prelude; opaque_encoders; logical_mappings;name;args;body}

let parse_lambda_str str = raw_parse_expr_str str |> convert_lambda StringSet.empty
let parse_expr_str str = raw_parse_expr_str str |> convert_expr
let parse_str str = raw_parse_str str |> convert
