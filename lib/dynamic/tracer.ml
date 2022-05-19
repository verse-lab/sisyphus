[@@@warning "-27-26-32-33"]
open Containers

module Symbol = Sisyphus_tracing.Symbol

module AH = Ast_helper
module AT = Asttypes

(* [type_ ty] converts a reified internal type [ty] into an AST
   expression encoding the corresponding type.

   raises [Failure] if given a internal type that does not contain
   enough information to be encoded as an OCaml type *)
let rec type_ (ty: Lang.Type.t) : Parsetree.core_type =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  match ty with
  | Lang.Type.Unit -> AH.Typ.constr (str @@ Longident.Lident "unit") []
  | Lang.Type.Var var -> AH.Typ.var (String.drop 1 var)
  | Lang.Type.Int -> AH.Typ.constr (str @@ Longident.Lident "int") []
  | Lang.Type.List ty -> AH.Typ.constr (str @@ Longident.Lident "list") [type_ ty]
  | Lang.Type.Array ty -> AH.Typ.constr (str @@ Longident.Lident "array") [type_ ty]
  | Lang.Type.Ref ty -> AH.Typ.constr (str @@ Longident.Lident "ref") [type_ ty]
  | Lang.Type.Product args -> AH.Typ.tuple (List.map type_ args)
  | Lang.Type.ADT (name, args, _) -> AH.Typ.constr (str @@ Longident.Lident name) (List.map type_ args)
  | Lang.Type.Loc -> failwith "locations not supported"
  | Lang.Type.Func -> failwith "higher order functions not supported"
  | Lang.Type.Val -> failwith "opaque vals not supported"

(* [encode_list exprs] given a list of AST expressions [exprs] returns
   an AST expression representing a list of those expressions *)
let encode_list exprs =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  let cons hd tl =
    AH.Exp.(construct (str Longident.(Lident "::")) (Some (tuple [hd; tl])))  in
  let nil = AH.Exp.construct (str Longident.(Lident "[]")) None in
  List.fold_right cons exprs nil

(* [encode_fun (arg, ty) body] returns an expression encoding a
   function with a single parameter [arg] with the explicit type
   constraint [ty] and body [body] *)
let encode_fun (arg, ty) body =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  AH.Exp.fun_ AT.Nolabel None
    (AH.Pat.constraint_ (AH.Pat.var (str arg)) (type_ ty))
    body

(* [encode_int n] will return an AST encoding the constant integer
   [n]. *)
let encode_int v =
  AH.Exp.constant (Pconst_integer (string_of_int v, None))

(* [encode_string str] will return an AST encoding the constant string
   [str]. *)
let encode_string v =
  AH.Exp.constant (Pconst_string (v, !AH.default_loc, None))

(* [build_enc_fun ty] returns an AST encoding a function to convert
   a value of type ty to the value type used in traces *)
let build_enc_fun v = 
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  let tmp_var_id_count = ref 0 in
  (* [fun f] builds a function whose body is f [var] where var is a fresh variable.

     Note: assumes user code doesn't use reserved variable __sisyphus_var_n for any n
     TODO: Check that this assumption holds in sanitisation *)
  let fun_ =
    fun f ->
      let var_name = "__sisyphus_enc_fun_var_" ^ string_of_int !tmp_var_id_count in
      incr tmp_var_id_count;
      let var =  AH.Pat.var (str var_name) in
      let exp = AH.Exp.ident (str Longident.(Lident var_name)) in
      AH.Exp.fun_ AT.Nolabel None var (f exp) in
  let rec build_enc_fun (v: Lang.Type.t) =
    let (let+) x f = Option.bind x f in
    match v with
    | Lang.Type.Unit -> None
    | Lang.Type.Ref _ -> None
    | Lang.Type.Array _ -> None
    | Lang.Type.Var _ ->
      Some (fun_ @@ fun v -> AH.Exp.variant "Value" (Some v))
    | Lang.Type.Int ->
      Some (fun_ @@ fun v -> AH.Exp.variant "Int" (Some v))
    | Lang.Type.Func -> None
    | Lang.Type.Val -> None
    | Lang.Type.Loc -> None
    | Lang.Type.List ty ->
      let+ ty_enc_fun = build_enc_fun ty in
      Some (fun_ @@ fun v -> AH.Exp.variant "List" AH.Exp.(Some (
        apply (ident (str @@ Longident.(Ldot ((Lident "List"), "map")))) [
          Nolabel, ty_enc_fun;
          Nolabel, v
        ]
      )))
    | Lang.Type.ADT (_adt, _tys, _) -> None
    | Lang.Type.Product tys ->
      let+ enc_funs = 
        List.map build_enc_fun tys
        |> List.all_some in
      let pat_vars =
        List.map (fun _ ->
          let id = !tmp_var_id_count in
          incr tmp_var_id_count;
          Printf.sprintf "__sisyphus_tuple_var_%d" id
        ) enc_funs in
      let exprs =
        List.combine enc_funs pat_vars
        |> List.map (fun (l,r) ->
          AH.Exp.apply l [Nolabel, AH.Exp.ident (str Longident.(Lident r))]
        ) in
      Some (AH.Exp.fun_
              AT.Nolabel None
              AH.Pat.((tuple (List.map (fun var -> AH.Pat.var (str var)) pat_vars)))
              (AH.Exp.variant "List" AH.Exp.(Some (encode_list exprs)))) in
  build_enc_fun v

(* [build_heap_enc_exp ty var] returns an AST expression, that, when
   evaluated, will encode the heap-based [var]'s value (either array or ref). *)
let build_heap_enc_exp (v: Lang.Type.t) var =
  let (let+) x f = Option.bind x f in
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  let list_map f ls =
    AH.Exp.(apply (ident (str Longident.(Ldot ((Lident "List"), "map")))) [
      Nolabel, f;
      Nolabel, ls
    ]) in
  let array_to_list a =
    AH.Exp.(apply (ident (str Longident.(Ldot ((Lident "Array"), "to_list")))) [ Nolabel, a ]) in
  let bang v =
    AH.Exp.(apply (ident (str Longident.(Lident "(!)"))) [ Nolabel, v ]) in

  match v with
  | Lang.Type.Array ty ->
    let+ enc_fun = build_enc_fun ty in
    Some (AH.Exp.variant "Array" @@ Some (
      list_map enc_fun (array_to_list (AH.Exp.ident (str Longident.(Lident var))))
    ))
  | Lang.Type.Ref ty -> 
    let+ enc_fun = build_enc_fun ty in
    Some (AH.Exp.variant "PointsTo" @@ Some (
      AH.Exp.apply enc_fun [
        Nolabel, bang (AH.Exp.ident (str Longident.(Lident var)))
      ]
    ))
  | _ -> None

let encode_env env =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  List.filter_map (fun (name, ty) ->
    build_enc_fun ty |> Option.map begin fun f ->
      AH.Exp.tuple [
        encode_string name;
        AH.Exp.apply f [Nolabel, AH.Exp.ident (str Longident.(Lident name))]
      ]
    end
  ) env
  |> encode_list

let encode_heap env =
  List.filter_map (fun (name, ty) ->
    build_heap_enc_exp ty name |> Option.map (fun exp ->
      AH.Exp.tuple [
        encode_string name;
        exp
      ]
    )
  ) env
  |> encode_list

let wrap_with_observe env ~at ~then_ =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  AH.Exp.sequence 
    AH.Exp.(apply (ident Longident.(str @@ Ldot ((Lident "Sisyphus_tracing"), "observe"))) [
      Labelled "at", encode_int at;
      Labelled "env", encode_env env;
      Labelled "heap", encode_heap env;
    ])
    then_

let encode_param (param: Lang.Expr.typed_param) =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  match param with
  | `Tuple pats ->
    (AH.Pat.tuple (List.map (fun (pat, ty) -> AH.Pat.constraint_ AH.Pat.(var (str pat)) (type_ ty)) pats))
  | `Var (pat,ty) ->
    AH.Pat.constraint_ AH.Pat.(var (str pat)) (type_ ty)

let rec encode_expr (expr: Lang.Expr.t) =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  match expr with
  | `Var v -> AH.Exp.ident Longident.(str (Lident v))
  | `App (f, args) ->
    let f =
      if String.contains f '.'
      then String.split_on_char '.' f |> Longident.unflatten
           |> Option.get_exn_or "invalid assumptions - attempted to call a malformed function"
      else Longident.Lident f in
    AH.Exp.(
      apply (ident Longident.(str f))
        (List.map (fun v -> (AT.Nolabel, encode_expr v)) args)
    )
  | `Int n -> encode_int n
  | `Constructor (name, []) ->
    AH.Exp.construct Longident.(str @@ Lident name) None
  | `Constructor (name, args) ->
    AH.Exp.construct Longident.(str @@ Lident name)
      (Some (AH.Exp.tuple (List.map encode_expr args)))
  | `Tuple elts ->
    AH.Exp.tuple (List.map encode_expr elts)
  | `Lambda (args, body) ->
    let encode_fun (param: Lang.Expr.typed_param) body =
      let pat = encode_param param in
      AH.Exp.fun_ Nolabel None pat body  in
    List.fold_right encode_fun args (encode_expr body)

let annotate ({ prelude; name; args; body }: Lang.Expr.t Lang.Program.t) : Parsetree.structure =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  let add_param (param: Lang.Expr.typed_param) env =
    match param with
    | `Tuple args -> env @ args
    | `Var arg -> env @ [arg] in
  let id =
    let id = ref 0 in
    fun () -> let vl = !id in incr id; vl in
  let rec encode_stmt ~observe env (stmt: Lang.Expr.t Lang.Program.stmt) =
    let wrap then_ =
      if observe then
        let id = id () in
        wrap_with_observe env ~at:id
          ~then_:(then_ ())
      else (then_ ()) in
    match stmt with
    | `Value vl ->
      wrap (fun () -> encode_expr vl)
    | `EmptyArray ->
      wrap (fun () -> AH.Exp.array [])
    | `LetExp (`Var (_, Lang.Type.Unit), _, expr, body) ->
      wrap (fun () -> AH.Exp.let_ Nonrecursive [ AH.Vb.mk (AH.Pat.any ()) (encode_expr expr) ]
              (encode_stmt ~observe env body)
           )
    | `LetExp (args, _, expr, body) ->
      let env = add_param args env in
      wrap (fun () -> AH.Exp.let_ Nonrecursive [ AH.Vb.mk (encode_param args) (encode_expr expr) ]
              (encode_stmt ~observe env body))
    | `LetLambda (var, `Lambda (params, lambody), body) ->
      AH.Exp.let_ Nonrecursive
        [ AH.Vb.mk (AH.Pat.var (str var)) (
            let env = List.fold_left (fun env param -> add_param param env) env params in
            List.fold_right (fun param exp -> AH.Exp.fun_ Nolabel None (encode_param param) exp) params @@
            encode_stmt ~observe:false env lambody) ]
        (let env = env @ [var, Func] in
         encode_stmt ~observe env body)
    | `Match (exp, cases) ->
      wrap (fun () -> AH.Exp.match_ (encode_expr exp) (List.map (fun (name, args, body) ->
        AH.Exp.case
          (AH.Pat.construct Longident.(str @@ Lident name)
             (match args with
              | [] -> None
              | args ->
                Some (AH.Pat.tuple
                        (List.map (fun (var, ty) ->
                           AH.Pat.constraint_ (AH.Pat.var (str var)) (type_ ty))
                           args))
             ))
          (let env = env @ args in
           encode_stmt ~observe env body)
      ) cases))
    | `Write (arr, offs, vl, body) ->
      wrap (fun () ->
        AH.Exp.sequence
          (AH.Exp.apply (AH.Exp.ident Longident.(str @@ Ldot (Lident "Array", "set"))) [
             Nolabel, AH.Exp.ident Longident.(str @@ Lident arr);
             Nolabel, AH.Exp.ident Longident.(str @@ Lident offs);
             Nolabel, encode_expr vl
           ])
          (encode_stmt ~observe env body)
      ) in
  let body = encode_stmt ~observe:true args body in
  let def =
    AH.Str.value
      AT.Nonrecursive [
      AH.Vb.mk
        AH.Pat.(var (str name))
        (List.fold_right encode_fun args body)
    ] in
  prelude @ [def]

module Generator = struct

  type long_ident = Longident.t

  let equal_long_ident l r =
    String.equal
      (Longident.flatten l |> String.concat ".")
      (Longident.flatten r |> String.concat ".")

  let pp_long_ident fmt l = Pprintast.longident fmt l
  let show_long_ident l = Format.to_string pp_long_ident l


  type arg_schema =
    | Unit
    | Symbol
    | Int
    | List of arg_schema
    | Array of arg_schema
    | Ref of arg_schema
    | Product of arg_schema list
    | Converted of long_ident * arg_schema
  [@@deriving show, eq]

  type schema = arg_schema list

  type instantiation = Parsetree.expression list

  let rec of_type (t: Lang.Type.t) =
    match t with
    | Lang.Type.Unit -> Unit
    | Lang.Type.Var _ -> Symbol
    | Lang.Type.Int -> Int
    | Lang.Type.List t -> List (of_type t)
    | Lang.Type.Array t -> Array (of_type t)
    | Lang.Type.Ref t -> Ref (of_type t)
    | Lang.Type.Product tys -> Product (List.map of_type tys)
    | Lang.Type.ADT (_, [arg], Some conv) ->
      let lid = String.split_on_char '.' conv |> Longident.unflatten |> Option.get_exn_or "invalid converter" in
      Converted (lid, of_type arg)
    | t -> failwith (Format.sprintf "unsupported argument type %a" Lang.Type.pp t)

  let extract_schema (prog: _ Lang.Program.t) : schema =
    prog.args |> List.map (fun (_, ty) -> of_type ty)

  let fresh_int =
    let next_id = ref 0 in
    fun () ->
      let id = !next_id in
      incr next_id;
      encode_int id

  let rec sample_expr (s: arg_schema) =
    let str str = Location.{ txt=str; loc= !AH.default_loc } in
    let open Random in
    match s with
    | Unit ->
      fun state -> AH.Exp.construct (str (Longident.Lident "()")) None
    | Symbol ->
      (* Sisyphus_tracing.Symbol.fresh () *)
      fun state -> AH.Exp.(
        apply
          (ident (str Longident.(Ldot (Ldot (Lident "Sisyphus_tracing", "Symbol"), "of_raw"))))
          [Nolabel, fresh_int ()]
      )
    | Int -> 
      let* i = Random.int 10 in
      pure @@ AH.Exp.constant (Pconst_integer (string_of_int i, None))
    | List ty ->
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_expr ty) |> list_seq in
      pure (encode_list contents)
    | Array ty -> 
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_expr ty) |> list_seq in
      pure @@ AH.Exp.array contents
    | Ref ty ->
      let* inner = sample_expr ty in
      pure @@ AH.Exp.(
        apply
          (ident @@ str @@ Longident.(Lident "ref"))
          [Nolabel, inner])
    | Product elts ->
      let* elts = List.map sample_expr elts |> list_seq in
      pure @@ AH.Exp.tuple elts
    | Converted (conv, ty) -> 
      let* sz = Random.pick_array [|1; 3; 4; 5; 8; 10; 20|] in
      let* contents = List.init sz (fun _ -> sample_expr ty) |> list_seq in
      pure @@ AH.Exp.(
        apply
          (ident @@ str @@ conv)
          [Nolabel, encode_list contents]
      )

  let sample (schema: schema) : instantiation =
    Random.run (Random.list_seq (List.map sample_expr schema))

end

module CompilationContext = struct

  module StringSet = Set.Make(String)
  type t = {
    mutable loaded_modules: StringSet.t;
    mutable evaluation_env: Evaluator.env
  }

  let init () =
    let env = Evaluator.initial_env () in
    let env = Evaluator.add_static_module_def ~mod_name:"Sisyphus_tracing"
                ~ast:(Evaluator.raw_parse_str [%blob "./sisyphus_tracing.ml"]) env in
    {
    loaded_modules=StringSet.empty;
    evaluation_env=env
  }

  let compile env file =
    if not @@ StringSet.mem file env.loaded_modules then begin
      env.loaded_modules <- StringSet.add file env.loaded_modules;
      env.evaluation_env <- Evaluator.dyn_load_module_from_file env.evaluation_env file
    end

  (** [eval_definition_with_annotations env ~deps ~prog] dynamically
     loads all the dependencies [dep] of program [prog] and returns a
     unique name to identify the function. *)
  let eval_definition_with_annotations =
    let fresh_mod_name =
      let trace_id = ref 0 in
      fun () ->
        incr trace_id;
        Printf.sprintf "Sisyphus_temporary_module_%d" !trace_id in
    fun env ~deps ~prog ->
      List.iter (compile env) deps;
      let mod_name = fresh_mod_name () in
      let ast = annotate prog in
      env.evaluation_env <-
        Evaluator.dyn_load_definition_as_module
          env.evaluation_env ~mod_name ~ast;
      Longident.(Ldot (Lident mod_name, prog.name))

  let eval env expr =
    Evaluator.eval_expr env.evaluation_env expr

end

type program = string list * Lang.Expr.t Lang.Program.t

let compile env ~deps ~prog =
  CompilationContext.eval_definition_with_annotations
    env ~deps ~prog

let generate_trace env prog input =
  let str str = Location.{ txt=str; loc= !AH.default_loc } in
  Sisyphus_tracing.trace
    (fun () -> (CompilationContext.eval env
                  AH.Exp.(apply (ident (str Longident.(Lident "ignore"))) [
                    Nolabel, apply (ident (str prog)) (List.map (fun v -> (AT.Nolabel, v)) input)
                  ])))
  
let bitrace env (deps1, prog1) (deps2, prog2) =
  let schema = Generator.extract_schema prog1 in
  assert (List.equal Generator.equal_arg_schema schema (Generator.extract_schema prog2));
  let prog1 = CompilationContext.eval_definition_with_annotations env ~deps:deps1 ~prog:prog1 in
  let prog2 = CompilationContext.eval_definition_with_annotations env ~deps:deps2 ~prog:prog2 in
  fun () -> 
    let input = Generator.sample schema in
    let trace1 = generate_trace env prog1 input in
    let trace2 = generate_trace env prog2 input in
    (trace1, trace2)
