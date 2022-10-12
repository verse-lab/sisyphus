open Containers

(** [is_pure lambda] given a [lambda], determines whether it is pure
    or not (assumes if any functions are called, they are also pure) *)
let is_pure (prog: [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) =
  let rec loop (stmt: Lang.Expr.t Lang.Program.stmt) =
    match stmt with
    | `Match (_, cases) ->
      List.for_all (fun (_, _, body) -> loop body) cases
    | `LetLambda (_, `Lambda (_, body), rest) ->
      loop body && loop rest
    | `EmptyArray -> true
    | `AssignRef _ | `IfThen _ -> false
    | `Write _ -> false
    | `Value _ -> true
    | `LetExp (_, _, _, rest) -> loop rest
    | `IfThenElse (_, l, r) -> loop l && loop r
  in
  match prog with
  | `Lambda (_, body) -> loop body

module StringSet = Set.Make (String)

let mut_vars (prog: Lang.Expr.t Lang.Program.stmt) : StringSet.t =
  let rec loop stmt (vars: StringSet.t) : StringSet.t =
    match stmt with
    | `Match (_, cases) -> List.fold_left (fun vars (_, _, c) -> loop c vars) vars cases
    | `LetLambda (_, `Lambda (_, body), rest) -> loop body vars |> loop rest
    | `IfThen (_, l, rest) -> loop l vars |> loop rest
    | `IfThenElse (_, l, r) -> loop l vars |> loop r
    | `LetExp (_, _, _, rest) -> loop rest vars
    | `EmptyArray | `Value _ -> vars
    | `Write (v, _, _, rest) -> loop rest (StringSet.add v vars)
    | `AssignRef (v, _, rest) -> loop rest (StringSet.add v vars)
  in
  loop prog (StringSet.empty)
