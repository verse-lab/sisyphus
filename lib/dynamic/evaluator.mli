type env

val raw_parse_str: string -> Parsetree.structure
(** [raw_parse_str txt] uses the OCaml compiler to parse a given string into structure AST. *)

val raw_parse_expr_str: string -> Parsetree.expression
(** [raw_parse_expr_str txt] uses the OCaml compiler to parse a given string into expression AST. *)

val raw_parse_channel:in_channel -> Parsetree.structure

val initial_env: unit -> env
(** [initial_env ()] returns an initial OCaml typing environment,
   preloaded with the OCaml stdlib.  *)

val dyn_load_definition_as_module: env -> mod_name:string -> ast:Parsetree.structure -> env
(** [dyn_load_definition_as_module env ~mod_name ~ast] compiles and
    dynamically loads/evaluates the AST [ast] under the module name
    [mod_name], returning an updated [env] *)

val dyn_load_module_from_file: env -> string -> env
(** [dyn_load_module_from_file env path] loads the source file at
    [path], compiles and evaluates it, returning an updated [env]
    with the module present. *)

val add_static_module_def: env -> mod_name:string -> ast:Parsetree.structure -> env
(** [add_static_module_def env ~mod_name ~ast] returns an updated
    [env] with the type signature of [ast] under a module [mod_name]
    included.

    NOTE: unlike [dyn_load_definition_as_module], this does not
    "evaluate" the AST [ast], but just updates the env to include
    it's signature. This is useful when you need to share modules
    between dynamically compiled code and host code. *)

val eval_expr: env -> Parsetree.expression -> 'a
(** [eval_expr env expr] compiles and evaluates the expression
    [expr] and returns the value.

    NOTE: The return type of this function is 'a (any type at
    all). You must explicitly annotate the return type at any call
    site, otherwise be prepared for possible memory corruption. *)

