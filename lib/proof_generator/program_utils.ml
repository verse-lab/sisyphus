open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"program utils" "prog utils"))

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

(** [mutated_vars lambda] when provided a [lambda], returns the set of
   heap variables (refs and pointers etc.) that the function mutates. *)
let mutated_vars (prog: [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ]) : StringSet.t =
  let rec loop stmt (vars: StringSet.t) : StringSet.t =
    match stmt with
    | `Match (_, cases) ->
      List.fold_left
        (fun vars (_, _, body) ->
           loop body vars) vars cases
    | `LetLambda (_, `Lambda (_, body), rest) ->
      let vars = loop body vars in
      loop rest vars
    | `IfThen (_, l, rest) ->
      let vars = loop l vars in
      loop rest vars
    | `IfThenElse (_, l, r) ->
      let vars = loop l vars in
      loop r vars
    | `LetExp (_, _, _, rest) ->
      loop rest vars
    | `EmptyArray  -> vars

    (* Note: when mutation occurs as the last statement of a block,
       the parser encodes it as an expression *)
    | `Write (arr, _, _, rest) ->
      let vars = StringSet.add arr vars in
      loop rest vars
    | `Value (`App ("Array.get", ([`Var arr; _; _]))) -> StringSet.add arr vars

    | `AssignRef (v, _, rest) ->
      let vars = StringSet.add v vars in
      loop rest vars
    | `Value (`App (":=", ([`Var v]))) -> StringSet.add v vars

    | `Value _ -> vars
  in
  match prog with
  | `Lambda (_, body) -> loop body (StringSet.empty)
