open Containers

type invariant = Lang.Expr.t * Lang.Expr.t array

module AT = Asttypes
module AH = Ast_helper

let var v = AH.Exp.ident (Location.mknoloc Longident.(Lident v))
let fvar v =
  let v = match v with
    | "TLC.LibList.app" -> "@"
    | "app" -> "@"
    | "TLC.LibList.combine" -> "List.combine"
    | "combine" -> "List.combine"
    | "TLC.LibList.concat" -> "@"
    | "concat" -> "@"
    | "TLC.LibList.drop" -> "Common.list_drop"
    | "drop" -> "Common.list_drop"
    | "TLC.LibList.map" -> "List.map"
    | "map" -> "List.map"
    | "TLC.LibList.rev" -> "List.rev"
    | "rev" -> "List.rev"
    | "TLC.LibList.split" -> "List.split"
    | "split" -> "List.split"
    | "TLC.LibList.take" -> "Common.list_take"
    | "take" -> "Common.list_take"
    | "TLC.LibListZ.drop" -> "Common.list_drop"
    | "TLC.LibListZ.length" -> "List.length"
    | "length" -> "List.length"
    | "TLC.LibListZ.sum" -> "Common.list_sum"
    | "sum" -> "Common.list_sum"
    | "TLC.LibListZ.take" -> "Common.list_take"
    | "TLC.LibOrder.ge" -> ">="
    | "TLC.LibOrder.le" -> "<="
    | "TLC.LibOrder.lt" -> "<"
    | "Coq.ZArith.BinInt.Z.max" -> "max"
    | "Coq.ZArith.BinInt.Z.min" -> "min"
    | "++" -> "@"
    | "make" -> "Common.list_make"
    | "TLC.LibListZ.make" -> "Common.list_make"
    | v -> v in
  Longident.unflatten (String.split_on_char '.' v)
  |> Option.value ~default:(Longident.(Lident v))
  |> Location.mknoloc
  |> AH.Exp.ident 


let extract_sym s = String.drop (String.length "symbol_") s

let sym_of_raw = Longident.Ldot (Ldot (Lident "Sisyphus_tracing", "Symbol"), "of_raw")
  

let rec evaluate_value (expr: Dynamic.Concrete.value) : Parsetree.expression =
  let cons h t =
    AH.Exp.construct Location.(mknoloc Longident.(Lident "::"))
      (Some (AH.Exp.tuple [h; t])) in
  let nil = AH.Exp.construct Location.(mknoloc Longident.(Lident "[]")) None in
  match expr with
  | `Tuple elts -> AH.Exp.tuple (List.map evaluate_value elts)
  | `List vls ->
    List.rev vls
    |> List.fold_left (fun t h -> cons (evaluate_value h) t) nil
  | `Int n ->
    AH.Exp.constant (Parsetree.Pconst_integer (string_of_int n, None))    
  | `Value s ->
    AH.Exp.apply (AH.Exp.ident Location.(mknoloc sym_of_raw)) [
      Nolabel, AH.Exp.constant (Pconst_integer (extract_sym s, None))
    ]
  | `Constructor (f, []) -> 
    AH.Exp.construct Location.(mknoloc Longident.(Lident f)) None
  | `Constructor (f, elts) -> 
    AH.Exp.construct Location.(mknoloc Longident.(Lident f))
      (Some (AH.Exp.tuple @@ List.map evaluate_value elts))
      

let rec evaluate_expression (expr: Lang.Expr.t) : Parsetree.expression =
  match expr with
  | `Tuple elts -> AH.Exp.tuple (List.map evaluate_expression elts)
  | `Var "true" -> AH.Exp.construct (Location.mknoloc Longident.(Lident "true")) None
  | `Var "false" -> AH.Exp.construct (Location.mknoloc Longident.(Lident "false")) None
  | `Var v -> var v
  | `App (f,args) ->
    AH.Exp.apply (fvar f) (List.map (fun exp -> (AT.Nolabel, evaluate_expression exp)) args)
  | `Lambda (params, body) ->
    List.fold_right (fun param body ->
      let param =
        match param with
        | `Tuple elts -> AH.Pat.tuple (List.map (fun (v, _) -> AH.Pat.var (Location.mknoloc v)) elts)
        | `Var (v,_) -> AH.Pat.var (Location.mknoloc v) in
      AH.Exp.fun_ AT.Nolabel None param body
    ) params (evaluate_expression body)
  | `Int n ->
    AH.Exp.constant (Parsetree.Pconst_integer (string_of_int n, None))
  | `Constructor (f, []) ->
    AH.Exp.construct (Location.mknoloc Longident.(Lident f)) None
  | `Constructor (f, args) ->
    AH.Exp.construct (Location.mknoloc Longident.(Lident f)) (Some (evaluate_expression (`Tuple args)))

let evaluate_typed_param (pat: Lang.Expr.typed_param) : Parsetree.pattern =
  match pat with
  | `Tuple args -> AH.Pat.tuple (List.map (fun (v, _) -> AH.Pat.var (Location.mknoloc v)) args)
  | `Var (v, _) -> AH.Pat.var (Location.mknoloc v)

let rec evaluate_stmt (stmt: Lang.Expr.t Lang.Program.stmt) : Parsetree.expression =
  match stmt with
  | `Match (exp, cases) ->
    AH.Exp.match_ (evaluate_expression exp) (List.map evaluate_case cases)
  | `EmptyArray -> AH.Exp.array []
  | `Value vl -> evaluate_expression vl
  | `LetExp (pat, _, body, rest) ->
    let pat = evaluate_typed_param pat in
    let body = evaluate_expression body in
    let rest = evaluate_stmt rest in
    AH.Exp.let_ Nonrecursive [
        AH.Vb.mk
          pat
          body
      ] rest
  | `LetLambda (name, lam, rest) ->
    let pat = AH.Pat.var (Location.mknoloc name) in
    let lam = evaluate_lambda lam in
    let rest = evaluate_stmt rest in
    AH.Exp.let_ Nonrecursive [
        AH.Vb.mk
          pat
          lam
      ] rest    
  | `Write (arr, ind, vl, rest) ->
    AH.Exp.sequence
    (AH.Exp.apply
      (AH.Exp.ident (Location.mknoloc Longident.(Ldot (Lident "Array", "set"))))
      [Nolabel, var arr;
       Nolabel, var ind;
       Nolabel, evaluate_expression vl ])
    (evaluate_stmt rest)
      
and evaluate_lambda (`Lambda (args, body)) =
  List.rev args
  |> List.fold_left (fun rest arg ->
    AH.Exp.fun_ Nolabel None (evaluate_typed_param arg) rest
  ) (evaluate_stmt body)


and evaluate_case (cons, args, body) : Parsetree.case =
  let pat =
    AH.Pat.construct Location.(mknoloc Longident.(Lident cons))
      (match args with
       | [] -> None
       | args -> Some (AH.Pat.tuple @@ List.map (fun (arg, _) -> AH.Pat.var (Location.mknoloc arg)) args)) in
  let body = evaluate_stmt body in
  AH.Exp.case pat body
  

let evaluate heap_vars ((pure, heap): invariant) : Parsetree.expression =
  let lident v = AH.Exp.ident (Location.mknoloc v) in
  let (&&) l r = AH.Exp.apply (var "&&") [AT.Nolabel, l; AT.Nolabel, r] in
  let (=) l r = AH.Exp.apply (var "=") [AT.Nolabel, l; AT.Nolabel, r] in
  let (!) l = AH.Exp.apply (var "!") [AT.Nolabel, l] in
  let arr_to_list l = AH.Exp.apply (lident (Longident.(Ldot (Lident "Array", "to_list")))) [AT.Nolabel, l] in
  let pure_assertion = evaluate_expression pure in
  let heap_assertions = 
    List.combine_shortest heap_vars (Array.to_list heap)
    |> List.map (fun (heap_var, array_vl) ->
      let vl = evaluate_expression array_vl in
      match heap_var with
      | v, `Ref ->
        (!(var v) = vl)
      | v, `Array ->
        ((arr_to_list (var v)) = vl)
    ) in
  AH.Exp.assert_ (List.fold_left (&&) pure_assertion heap_assertions)
