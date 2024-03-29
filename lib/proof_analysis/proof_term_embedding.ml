open Containers

type invariant = Lang.Expr.t * Lang.Expr.t array

module AT = Asttypes
module AH = Ast_helper

let var v = AH.Exp.ident (Location.mknoloc Longident.(Lident v))
let fvar v =
  let v = match v with
    | "make" -> "Common.list_make"
    | "TLC.LibListZ.make" -> "Common.list_make"
    | v -> v in
  Longident.unflatten (String.split_on_char '.' v)
  |> Option.value ~default:(Longident.(Lident v))
  |> Location.mknoloc
  |> AH.Exp.ident 

let extract_sym s =
  match String.drop (String.length "symbol_") s |> String.split_on_char '_' with
  | [sym; id] -> (sym,id)
  | _ -> Format.ksprintf ~f:failwith "unexpected format for symbol value %s" s

let sym_of_raw = Longident.Ldot (Ldot (Lident "Sisyphus_tracing", "Symbol"), "of_raw")

let cons h t =
  AH.Exp.construct Location.(mknoloc Longident.(Lident "::"))
    (Some (AH.Exp.tuple [h; t]))

let rec embed_value (expr: Dynamic.Concrete.value) : Parsetree.expression =
  let nil = AH.Exp.construct Location.(mknoloc Longident.(Lident "[]")) None in
  match expr with
  | `Tuple elts -> AH.Exp.tuple (List.map embed_value elts)
  | `List vls ->
    List.fold_right (fun h t -> cons (embed_value h) t) vls nil
  | `Int n ->
    AH.Exp.constant (Parsetree.Pconst_integer (string_of_int n, None))    
  | `Bool true ->
    AH.Exp.construct ({Location.txt = Longident.(Lident "true"); loc = Location.none})  None    
  | `Bool false ->
    AH.Exp.construct ({Location.txt = Longident.(Lident "false"); loc = Location.none})  None    
  | `Value s ->
    let (sym, id) = extract_sym s in
    AH.Exp.apply (AH.Exp.ident Location.(mknoloc sym_of_raw)) [
      Nolabel, AH.Exp.tuple [AH.Exp.constant (Pconst_integer (id, None)); AH.Exp.constant (Pconst_string (sym, Location.none, None))]
    ]
  | `Constructor (f, []) -> 
    AH.Exp.construct Location.(mknoloc Longident.(Lident f)) None
  | `Constructor (f, elts) -> 
    AH.Exp.construct Location.(mknoloc Longident.(Lident f))
      (Some (AH.Exp.tuple @@ List.map embed_value elts))
  | `Opaque (f, elts) ->
    AH.Exp.apply (fvar f) [Nolabel, (List.fold_right (fun h t -> cons (embed_value h) t) elts nil)]

let rec embed_expression (expr: Lang.Expr.t) : Parsetree.expression =
  match expr with
  | `Tuple elts -> AH.Exp.tuple (List.map embed_expression elts)
  | `Var "true" -> AH.Exp.construct (Location.mknoloc Longident.(Lident "true")) None
  | `Var "false" -> AH.Exp.construct (Location.mknoloc Longident.(Lident "false")) None
  | `Var v -> var v
  | `App (f,args) ->
    AH.Exp.apply (fvar f) (List.map (fun exp -> (AT.Nolabel, embed_expression exp)) args)
  | `Lambda (params, body) ->
    List.fold_right (fun param body ->
      let param =
        match param with
        | `Tuple elts -> AH.Pat.tuple (List.map (fun (v, _) -> AH.Pat.var (Location.mknoloc v)) elts)
        | `Var (v,_) -> AH.Pat.var (Location.mknoloc v) in
      AH.Exp.fun_ AT.Nolabel None param body
    ) params (embed_expression body)
  | `Int n ->
    AH.Exp.constant (Parsetree.Pconst_integer (string_of_int n, None))
  | `Constructor (f, []) ->
    AH.Exp.construct (Location.mknoloc Longident.(Lident f)) None
  | `Constructor (f, [expr]) ->
    AH.Exp.construct (Location.mknoloc Longident.(Lident f)) (Some (embed_expression expr))
  | `Constructor (f, args) ->
    AH.Exp.construct (Location.mknoloc Longident.(Lident f)) (Some (embed_expression (`Tuple args)))

let embed_typed_param (pat: Lang.Expr.typed_param) : Parsetree.pattern =
  match pat with
  | `Tuple args -> AH.Pat.tuple (List.map (fun (v, _) -> AH.Pat.var (Location.mknoloc v)) args)
  | `Var (v, _) -> AH.Pat.var (Location.mknoloc v)

let rec embed_stmt (stmt: Lang.Expr.t Lang.Program.stmt) : Parsetree.expression =
  match stmt with
  | `Match (exp, cases) ->
    AH.Exp.match_ (embed_expression exp) (List.map embed_case cases)
  | `EmptyArray -> AH.Exp.array []
  | `Value vl -> embed_expression vl
  | `LetExp (pat, _, body, rest) ->
    let pat = embed_typed_param pat in
    let body = embed_expression body in
    let rest = embed_stmt rest in
    AH.Exp.let_ Nonrecursive [ AH.Vb.mk pat body ] rest
  | `LetLambda (name, lam, rest) ->
    let pat = AH.Pat.var (Location.mknoloc name) in
    let lam = embed_lambda lam in
    let rest = embed_stmt rest in
    AH.Exp.let_ Nonrecursive [ AH.Vb.mk pat lam ] rest
  | `Write (arr, ind, vl, rest) ->
    AH.Exp.sequence
      (AH.Exp.apply
         (AH.Exp.ident (Location.mknoloc Longident.(Ldot (Lident "Array", "set"))))
         [Nolabel, var arr;
          Nolabel, var ind;
          Nolabel, embed_expression vl ])
      (embed_stmt rest)    
  | `IfThen (cond, left, rest) ->
    let cond = embed_expression cond in
    let left = embed_stmt left in
    AH.Exp.sequence
      (AH.Exp.ifthenelse cond left None) 
      (embed_stmt rest)    
  | `IfThenElse (cond, left, right) ->
    let cond = embed_expression cond in
    let left = embed_stmt left in
    let right = embed_stmt right in
    AH.Exp.ifthenelse cond left (Some right)
  | `AssignRef (arr, vl, rest) ->
    AH.Exp.sequence
      (AH.Exp.apply
         (AH.Exp.ident (Location.mknoloc Longident.(Lident ":=")))
         [Nolabel, var arr; Nolabel, embed_expression vl ])
      (embed_stmt rest)


and embed_lambda (`Lambda (args, body)) =
  List.rev args
  |> List.fold_left (fun rest arg ->
    AH.Exp.fun_ Nolabel None (embed_typed_param arg) rest
  ) (embed_stmt body)

and embed_case (cons, args, body) : Parsetree.case =
  let pat =
    AH.Pat.construct Location.(mknoloc Longident.(Lident cons))
      (match args with
       | [] -> None
       | args -> Some (AH.Pat.tuple @@
                       List.map (fun (arg, _) -> AH.Pat.var (Location.mknoloc arg)) args)) in
  let body = embed_stmt body in
  AH.Exp.case pat body
