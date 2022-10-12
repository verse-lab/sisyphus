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
