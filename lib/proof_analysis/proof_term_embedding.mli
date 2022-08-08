
(** [embed_value expr] embeds an observed value [expr] as a constant
    parsetree expression.  *)
val embed_value : Dynamic.Concrete.value -> Parsetree.expression

(** [embed_expression expr] embeds a reified expression [expr] to its
    corresponding reified OCaml AST representation.  *)
val embed_expression : Lang.Expr.t -> Parsetree.expression

(** [embed_typed_param pat] embeds a pattern [pat] into its OCaml AST representation.  *)
val embed_typed_param : Lang.Expr.typed_param -> Parsetree.pattern

(** [embed_stmt stmt] embeds a reified program stmt [stmt] into its
    OCaml AST representation.  *)
val embed_stmt : Lang.Expr.t Lang.Program.stmt -> Parsetree.expression

(** [embed_lambda lambda] embeds a reified functional value [lambda] into its
    OCaml AST representation.  *)
val embed_lambda :
  [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ] -> Parsetree.expression

(** [embed_case case] embeds a match case [case] into its OCaml AST
    representation.  *)
val embed_case :
  string * (string * Lang.Type.t) list * Lang.Expr.t Lang.Program.stmt -> Parsetree.case
