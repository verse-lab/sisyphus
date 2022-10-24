open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Generates candidate invariants" "gen"))

module ExprSet = Set.Make(Lang.Expr)
module TypeSet = Set.Make(Lang.Type)

let split_last =
  let rec loop last acc = function
    | [] -> List.rev acc, last
    | h :: t -> loop h (last :: acc) t in
  function
    [] -> invalid_arg "split_last called on empty list"
  | h :: t -> loop h [] t

let drop_last ls =
  let rec loop acc = function
    | [] | [_] -> List.rev acc
    | h :: t -> loop (h :: acc) t in
  loop [] ls

let combine_rem xz yz =
  let rec loop acc xz yz =
    match xz, yz with
    | [], [] -> List.rev acc, None
    | _ :: _ as xz, [] -> List.rev acc, Some (Either.Left xz)
    | [], (_ :: _ as yz) -> List.rev acc, Some (Either.Right yz)
    | x :: xz, y :: yz -> loop ((x, y) :: acc) xz yz in
  loop [] xz yz

let seq_force ls =
  let rec loop i acc ls =
    match ls () with
    | Seq.Nil -> i, List.rev acc
    | Seq.Cons (h, t) ->
      loop (i + 1) (h :: acc) t in
  let (sz, ls) = loop 0 [] ls in
  sz, Seq.of_list ls


let reduce pure =
  let no_pure_original = List.length pure in
  let pure = ExprSet.of_list pure |> ExprSet.to_list in
  let no_pure_updated = List.length pure in
  Log.debug (fun f -> f "reduced %d -> %d unique@." no_pure_original no_pure_updated);
  pure

(** [asserts cond f] asserts that [cond] is true, and if not, fails
    with the error produced by [f]. *)
let asserts b f =
  if not b then
    failwith (f (Format.ksprintf ~f:failwith))

let show_obs obs = [%show: (string * Dynamic.Concrete.value) list * (string * Dynamic.Concrete.heaplet) list] obs

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name)

let arg_list_to_str args =
  (List.map (function
     | `Type ty -> "(" ^ Proof_utils.Printer.show_ty ty ^ ")"
     | `Untyped vl -> "(" ^ Proof_utils.Printer.show_expr vl ^ ")"
     | `Typed (vl, ty) -> "(" ^ Proof_utils.Printer.show_expr vl ^ ": " ^ Proof_utils.Printer.show_ty ty ^ ")"
   ) args
   |> String.concat " ")

let find_spec t const =
  Proof_context.search t [
    true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
    true, Search.(GlobSearchLiteral
                    (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef const))))
  ] |> function
  | [(Names.GlobRef.ConstRef name, _, ty)] -> (name, ty)
  | [_] -> failwith "failure finding specification for function application: non-constant name for reference"
  | [] ->
    Format.ksprintf ~f:failwith
      "failure finding specification for function application of %s: could not find an appropriate specification"
      (Names.Constant.to_string const)
  | _ -> failwith "failure finding specification for function application: ambiguity - more than one valid specification found"

type constr = Constr.constr
let pp_constr fmt v =
  Format.pp_print_string fmt @@ Proof_utils.Debug.constr_to_string v

type expr = Lang.Expr.t
let pp_expr fmt vl = Pprintast.expression fmt (Proof_analysis.Embedding.embed_expression vl)

type name = Names.Name.t
let pp_name fmt vl = Format.fprintf fmt "%s" (name_to_string vl)

let expr_contains_free_variables expr =
  Lang.Expr.fold (fun contains_fv -> fun expr ->
    contains_fv || match expr with `Var _ -> true | _ -> false
  ) false expr

let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

(* [is_typed_combinator lemma_name] determines if [lemma_name] refers
   to one of Sisyphus' specialised fold combinators which takes an
   explicit type parameter as its first argument.

   Why is this required? Because Coq is unable to infer this type
   automatically from the concrete arguments themselves, as the type
   of this parameter isn't constrained by the input argument. If we
   didn't make it explict, then when we attempt to calculate the type
   of the combinator on concrete arguments, we would receive an unable
   to find an instance error.
*)
let is_typed_combinator lemma_name =
  match Names.Constant.to_string lemma_name with
  | "Common.Verify_combinators.until_upto_spec" | "Common.Verify_combinators.until_downto_spec"
  | "Common.Verify_combinators.nat_fold_up_spec" | "Common.Verify_combinators.nat_fold_down_spec" ->
    true
  | _ -> false

(* [is_option_combinator lemma_name] determines if [lemma_name] refers
   to one of Sispyhus' specialised fold combinators which take an
   explicit type parameter as its first argument.  *)
let is_option_combinator lemma_name =
  match Names.Constant.to_string lemma_name with
  | "Common.Verify_combinators.until_upto_spec" | "Common.Verify_combinators.until_downto_spec" -> true
  | _ -> false



let rec update_program_id_over_lambda (t: Proof_context.t)
          (`Lambda (_, body): [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ])  =
  let rec loop (body: Lang.Expr.t Lang.Program.stmt) = match body with
    | `Match (_, cases) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      List.iter (fun (_, _, body) -> loop body) cases
    |`AssignRef (_, _, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop body
    | `Write (_, _, _, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop body
    | `LetLambda (_, lambody, body) ->
      update_program_id_over_lambda t lambody;
      loop body
    | `LetExp (_, _, _, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop body
    | `EmptyArray ->
      t.current_program_id <- Lang.Id.incr t.current_program_id
    | `Value _ ->
      t.current_program_id <- Lang.Id.incr t.current_program_id
    | `IfThenElse (_, then_, else_) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop then_;
      loop else_
    | `IfThen (_, then_, body) ->
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      loop then_;
      loop body in
  loop body



(** [instantiate_expr t env obs (expr, ty)] attempts to instantiate a
    concrete argument [expr] using observed values [obs] from an
    execution trace.  To do this, it may introduce additional evars in
    proof context [t] to represent polymorphic values. *)
let instantiate_expr t env (ctx, heap_ctx) (vl,ty) =
  let lookup_var v ty =
    Log.debug (fun f -> f "Key list is [%a]"
                          (List.pp String.pp)
                          (StringMap.keys env.Proof_env.bindings |> List.of_iter));
    begin match StringMap.find_opt v env.Proof_env.bindings with
    | None -> Some (`Var v)
    | Some v ->
      Option.or_lazy
        (List.Assoc.get ~eq:String.equal v ctx
         |> Option.flat_map (Proof_context.eval_tracing_value t ty))
        ~else_:(fun () ->
          List.Assoc.get ~eq:String.equal v heap_ctx
          |> Option.flat_map (function
            | `Array ls -> 
              begin match ty with
              | Lang.Type.List ty -> Proof_context.eval_tracing_list t ty ls
              | _ -> None
              end
            | `PointsTo vl -> Proof_context.eval_tracing_value t ty vl
          )
        )
    end in
  let lookup_var v ty =
    let res = lookup_var v ty in
    Log.debug (fun f -> f "lookup_var %s %a ==> %a@." v  Lang.Type.pp ty (Option.pp Lang.Expr.pp) res);
    res in
  let rec instantiate_expr (vl, ty) =
    match vl, ty with
    | `Var v, ty ->
      Log.debug (fun f -> f "instantiate_expr called on (%s, %a) ==> looking up" v Lang.Type.pp ty);
      (lookup_var v ty) |> Option.map (fun vl -> (vl, ty))
    | (`Constructor ("::", [h;t])), (Lang.Type.List ty as ty_ls) ->
      let result =
        let open Option in
        let* (h, _) = instantiate_expr (h, ty) in
        let* (t, _) = instantiate_expr (t, ty_ls) in
        Some (`Constructor ("::", [h; t]), ty_ls) in
      Option.or_ result ~else_:(Some (vl, ty))
    | (`Tuple elts), Lang.Type.Product tys when List.compare_lengths elts tys = 0 ->
      List.combine elts tys
      |> List.map instantiate_expr
      |> List.all_some
      |> Option.map (fun elts -> (`Tuple (List.map fst elts), ty))
      |> Option.or_ ~else_:(Some (vl, ty))
    | `App (f, args) as expr, ty ->
      Log.debug (fun p -> p "found app of %s => attempting to instantiate arguments" f);
      let res =
        let open Option in
        let* args =
          List.map (fun exp ->
            let* ty = Proof_context.typeof_opt t (Format.to_string Proof_utils.Printer.pp_expr exp) in
            let* ty = Proof_utils.CFML.extract_typ_opt ty in
            Some (exp, ty)
          ) args
          |> List.all_some in
        Log.debug (fun p ->
          p "in app of %s => was able to type all arguments: %a" f
            (List.pp (Pair.pp Lang.Expr.pp Lang.Type.pp)) args);
        let* args =
          List.map instantiate_expr args
          |> List.all_some in
        Log.debug (fun p ->
          p "in app of %s => was able to instantiate all arguments: %a" f
            (List.pp (Pair.pp Lang.Expr.pp Lang.Type.pp)) args);
        let args = List.map fst args in
        Some (`App (f, args), ty) in
      Option.or_ ~else_:(Some (expr, ty)) res
    | expr, ty -> Some (expr, ty) in

  instantiate_expr (vl,ty)

let instantiate_arguments_with_evars t lemma_name init_params =
  let mk_lemma_instantiated_type params =
    let term =
      Format.sprintf
        "%s %s"
        (Names.Constant.to_string lemma_name)
        (arg_list_to_str params) in
    Log.debug (fun f -> f "proof context is:\n%s" (Proof_context.extract_proof_script t));
    Log.debug (fun f -> f "pose proof (%s)." term);
    Proof_context.typeof t term in
  let rec loop params lemma_instantiated_type =
    match Constr.kind lemma_instantiated_type with
    | Prod (Context.{binder_name; _}, ty, _) ->
      let evar_name =
        let base = match binder_name with
          | Names.Name.Anonymous -> None
          | Names.Name.Name _ -> Some (name_to_string binder_name) in
        let new_name = Proof_context.fresh ?base t in
        new_name in
      Proof_context.append t "evar (%s: %s)." evar_name
        (Proof_utils.Debug.constr_to_string_pretty ty);
      let params = params @ [`Untyped (`Var evar_name)] in
      let lemma_instantiated_type = mk_lemma_instantiated_type params in
      loop params lemma_instantiated_type
    | _ -> params, lemma_instantiated_type in
  let init_ty = mk_lemma_instantiated_type init_params in
  loop init_params init_ty

(** [build_complete_params t env obs lemma_name init_params] returns a pair
    ([complete_params], [head_ty]) where [complete_params] a list of
    concrete arguments to the specification defined by [lemma_name]. To
    do this, it starts with [init_params] and then updates the proof
    context [t] with fresh existential variables for each remaining
    argument.

    Note: assumes that no subsequent arguments past [init_params] are
    implicit. *)
let build_complete_params t env obs ~inv lemma_name init_params logical_params =
  let mk_lemma_instantiated_type params =
    let term =
      Format.sprintf
        "%s %s" (Names.Constant.to_string lemma_name) (arg_list_to_str params) in
    Proof_context.typeof t term in

  let init_ty = mk_lemma_instantiated_type init_params in

  (* first, apply the specification to an evar representing the invariant *)
  let init_params, inv =
    asserts (Constr.isProd init_ty) (fun f -> f "expected invariant to be arrow type");
    let (Context.{binder_name; _}, ty, _) = Constr.destProd init_ty in
    asserts (Names.Name.is_name binder_name) (fun f -> f "expected first argument to be the invariant, and thus named");
    let base = Format.to_string Pp.pp_with @@ Names.Name.print binder_name in
    let fresh_inv_name = Proof_context.fresh ~base t in
    Proof_context.append t "evar (%s: %s)." fresh_inv_name (Proof_utils.Debug.constr_to_string_pretty ty);
    init_params @ [`Untyped (`Var fresh_inv_name)], (fresh_inv_name, snd inv) in
  (* re calculate the type: *)
  let init_ty = mk_lemma_instantiated_type init_params in

  Log.debug (fun f -> f "initial type before evaring is %s" (Proof_utils.Debug.constr_to_string_pretty init_ty));
  let pre_heap = Proof_utils.CFML.extract_pre_heap init_ty in

  Log.debug (fun f -> f "pre heap is %s" ([%show: [ `Impure of string * Lang.Type.t | `Pure of constr ] list ] pre_heap));
  Log.debug (fun f -> f "obs is %s" (show_obs obs));

  (* finally, for any logical params, assume they match the heaplets
     in order, so retrieve the observations for the heap values
     instead: *)
  let _, init_params =
    let logical_instantiations =
      List.combine_shortest logical_params pre_heap in
    List.fold_left (fun (init_ty, init_params) binding ->
      match binding, Constr.kind_nocast init_ty with
      | (_, `Impure (name, _)), Constr.Prod (_, ty, init_ty) ->
        let ty = Proof_utils.CFML.extract_typ ty in
        let instantiated = instantiate_expr t env obs (`Var name, ty) in
        let param = Option.map (fun res -> `Typed res) instantiated
                    |> Option.get_exn_or (Format.sprintf "failed to instantiate") in
        (init_ty, init_params @ [param])
      | _ -> failwith "Don't know how to instantiate logical parameters"
    ) (init_ty, init_params) logical_instantiations in

  let params, _ = instantiate_arguments_with_evars t lemma_name init_params in
  params, inv


(** [instantiate_arguments t env args (ctx, heap_ctx)] attempts to
    instantiate a list of concrete arguments [args] using an observed
    context [ctx] and heap state [heap_ctx] from an execution trace.
    To do this, it may introduce additional evars in proof context [t]
    to represent polymorphic values. *)
let instantiate_arguments t env args obs =
  List.map (function
    (* only pure arguments should be instantiated as arguments directly *)
    | (`Var _, (Lang.Type.List _ | Lang.Type.ADT ("option", _, _) | Lang.Type.Int | Lang.Type.Bool | Lang.Type.Unit)) as v ->
      instantiate_expr t env obs v
    (* otherwise, if we have a variable, leave it as it is *)
    | (`Var _, _) as v -> Some v
    | v -> instantiate_expr t env obs v
  ) args
  |> List.all_some

(** [ensure_single_invariant ~name ~ty ~args] when given the
    application of lemma [name] to arguments [args], where [name] has
    type [ty], ensures that [name] refers to a specification of the
    correct type. *)
let ensure_single_invariant ~name:lemma_name ~ty:lemma_full_type ~args:f_args  =
  (* split lemma type into - params, invariants, and spec  *)
  let (lemma_params, lemma_invariants, spec) = Proof_utils.CFML.extract_spec lemma_full_type in
  (* use coq's internals to drop any implicit parameters  *)
  let explicit_lemma_params = Proof_utils.drop_implicits lemma_name lemma_params in

  (* TODO: generalise this somehow? *)
  (* special case for until and fold combinators, which take their accumulator type as an explicit first parameter   *)
  let explicit_lemma_params =
    if is_typed_combinator lemma_name
    then List.drop 1 explicit_lemma_params
    else explicit_lemma_params in

  (* we assume that the first explicit arguments to the lemma match the arguments to the function  *)
  let param_bindings, remaining = combine_rem explicit_lemma_params f_args in
  match remaining with
  | Some (Right _) | None | Some (Left [])  ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with no invariant/insufficient arguments?"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left ((_, inv_ty) :: logical_params)) when (* it is invalid for, either: *)
      (not (Proof_utils.CFML.is_invariant_ty inv_ty) (* first argument after concrete to not be an invariant *)
       || List.exists (Pair.snd_map Proof_utils.CFML.is_invariant_ty) logical_params)
    (*  or any arguments after the invariant to be hprop-taking *) ->
    Format.ksprintf ~f:failwith "TODO: found function application %a zero or more than one invariants"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left (_ :: [])) ->
    []
  | Some (Left (_ :: logical_params)) ->
    let logical_params =
      List.map (fun (name, _) ->
        name_to_string name)
        logical_params in
    logical_params

let typeof ?(product_types=[]) t env (s: string) : (Lang.Type.t list * Lang.Type.t) list =
  let ty =
    match s with
    | "++" ->
      List.map
        (fun v ->
           Lang.Type.([List (Var v); List (Var v)], List (Var v)))
        env.Proof_env.poly_vars
    | "option_value_fst" ->
      List.map Lang.Type.(fun ((t1, t2)) ->  ([t1; ADT ("option", [Product [t1;t2]], None)], t1)) product_types
    | "option_value_snd" ->
      List.map Lang.Type.(fun ((t1, t2)) ->  ([t2; ADT ("option", [Product [t1;t2]], None)], t2)) product_types
    | "Opt.option_is_some"
    | "is_some" ->
      List.map (fun ty ->
        Lang.Type.([ADT ("option", [ty], None)], Bool)
      ) ((List.map (fun v -> Lang.Type.Var v) env.poly_vars) @
         List.map (fun (t1, t2) -> Lang.Type.Product [t1;t2]) product_types)
    | "not" -> Lang.Type.[[Bool], Bool]
    | "-" -> Lang.Type.[[Int; Int], Int]
    | "+" -> Lang.Type.[[Int; Int], Int]
    | "=" -> []
    | s when not (String.exists Char.(fun c -> ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')) s) ->
      Format.ksprintf ~f:failwith "found unknown operator %s" s
    | s ->
      let (let+) x f = Option.bind x f in
      Option.value ~default:[] @@
      let+ ty = (Proof_context.typeof_opt t s) in
      let+ name = Proof_context.names t s in
      match name with
      | Names.GlobRef.ConstRef s ->
        Log.debug (fun f -> f "checking the typeof %s ==> %s@.full:%s" (Names.Constant.to_string s)
                              (Proof_utils.Debug.constr_to_string_pretty ty)
                              (Proof_utils.Debug.constr_to_string ty));
        let Lang.Type.Forall (poly, args) = Proof_utils.CFML.extract_fun_typ ~name:s ty in
        let instantiations =
          match env.Proof_env.poly_vars with 
          | (_ :: _) as poly_vars ->
            List.map_product_l (fun pv -> List.map (fun var -> Lang.Type.(pv, var)) poly_vars) poly
            |> List.map (fun subst ->
              let subst = StringMap.of_list subst in
              let map v = StringMap.find_opt v subst
                          |> Option.value ~default:v in
              List.map (Lang.Type.map_poly_var map) args
              |> split_last)
          | [] ->
            let poly_vars = [Lang.Type.Int] in (* TODO: draw this from the arguments/env *)
            List.map_product_l (fun pv -> List.map (fun var -> Lang.Type.(pv, var)) poly_vars) poly
            |> List.map (fun subst ->
              let subst = StringMap.of_list subst in
              List.map (Lang.Type.subst subst) args
              |> split_last
            ) in
        Some (instantiations)
      | n ->
        Log.debug (fun f -> f "%s mapped to non const ref %s" s (Proof_utils.Debug.globref_to_string n));
        None in
  Log.debug (fun f -> f "typeof [%s] ==> [%s]@." s ([%show: (Lang.Type.t list * Lang.Type.t) Containers.List.t] ty));
  ty

let renormalise_name t (s: string) : string option =
  let (let+) x f = Option.bind x f in
  let s_norm =
    match s with
    | "++" -> Some "TLC.LibList.app"
    | "-" -> Some "-"
    | "+" -> Some "+"
    | s ->
      try
        let s_base = String.split_on_char '.' s |> List.last_opt |> Option.value ~default:s in
        let+ name = Proof_context.names t s_base in
        match name with
        | Names.GlobRef.ConstRef s ->
          Some (Names.Constant.to_string s)
        | _ -> None
      with
      | _ -> None in
  (* Log.debug (fun f -> f "checking the type of %s -> %s\n@." s ([%show: (Lang.Type.t list * Lang.Type.t) Containers.Option.t] ty)); *)
  Option.map (fun s ->
    if String.prefix ~pre:"TLC.LibListZ." s
    then "TLC.LibList." ^ String.drop (String.length "TLC.LibListZ.") s
    else s)
    s_norm

(* [calculate_inv_ty t ~f ~args] calculates the type of the invariant
   required in order to symbolically execute lemma [f] on arguments
   [args] *)
let calculate_inv_ty t ~f:lemma_name ~args:f_args =
  let combinator_ty = 
    if is_typed_combinator lemma_name
    then 
      let ty = Proof_utils.CFML.extract_xapp_type (Proof_context.current_goal t).ty in
      let ty =
        if is_option_combinator lemma_name
        then match ty with | Lang.Type.ADT ("option", [ty], _) -> ty
                           | _ -> Format.ksprintf ~f:failwith "invalid option combinator type %a" Lang.Type.pp ty
        else ty in
      Some (`Type ty)
    else None in
  let instantiated_spec =
    let args = Option.to_list combinator_ty @ List.map (fun (v, ty) -> `Typed (v, ty)) f_args in
    Format.sprintf "%s %s" (Names.Constant.to_string lemma_name)
      (arg_list_to_str args) in
  let instantiated_spec = (Proof_context.typeof t instantiated_spec) in
  let (Context.{binder_name; _}, ty, rest) = Constr.destProd instantiated_spec in

  let framed_heaplets = 
    let (_, _, body) = Proof_utils.CFML.extract_spec rest in
    let _, args = Constr.destApp body in
    let heaplets = match Proof_utils.CFML.extract_heap args.(3) with
      | `Empty -> []
      | `NonEmpty ls -> ls in
    List.fold_left (fun fns trm ->
      match trm with
      | `Pure _ -> fns
      | `Impure f ->
        match Constr.kind_nocast f with
        | Constr.App (f, [| _; _; var |]) when Proof_utils.CFML.is_const_named "repr" f ->
          let var = if Constr.isCast var then let (c, _, _) = Constr.destCast var in c else var in
          let id = Constr.destVar var in
          StringSet.add (Names.Id.to_string id) fns
        | _ -> fns
    ) StringSet.empty heaplets in

  let tys = Proof_utils.CFML.unwrap_invariant_type ty in
  let tys = List.mapi (fun i v -> Format.sprintf "arg%d" i, v) tys in
  framed_heaplets, combinator_ty, (name_to_string binder_name, tys)

(** [reduce_term t term] reduces a proof term [term] using ultimate
    reduction.  *)
let reduce_term t term =
  let filter ~path ~label =
    match path, label with
    (* | "Coq.Init.Logic.eq_ind" when Option.is_some !eq_ind_reduce_name ->
     *   `Subst (fst @@ Option.get_exn_or "invalid assumptions" !eq_ind_reduce_name) *)
    | ("Coq.ZArith.BinInt.Z"
      | "Coq.ZArith.BinIntDef.Z"
      | "Coq.ZArith.Znat.Nat2Z"
      | "Coq.ZArith.Znat.Zabs2Nat"
      | "Coq.ZArith.Znat"
      | "Coq.micromega.ZifyInst"
      | "Coq.Init.Nat"
      | "Coq.PArith.BinPos.Pos"
      | "Coq.Init.Peano"
      | "Coq.micromega.Tauto"
      | "Coq.micromega.VarMap"
      | "Coq.micromega.ZifyClasses"
      | "Coq.micromega.ZMicromega"
      | "Coq.Init.Wf"
      | "Coq.Init.Datatypes"
      | "Coq.Classes.Morphisms"
      | "Coq.Init.Logic"
      | "Coq.Arith.PeanoNat.Nat"
      | "Coq.Bool.Bool"
      | "Coq.Classes.RelationClasses"
      ), _
      -> `KeepOpaque
    | "TLC.LibInt", "le_zarith" -> `KeepOpaque
    | "CFML.SepBase.SepBasicSetup.SepSimplArgsCredits", _ ->
      (* no point expanding the SepSimplArgsCredits lemmas as they just rearrange heaplets *)
      `KeepOpaque
    (* keep the reflection lemmas opaque, as they expand into cases that can't be reduced  *)
    | "TLC.LibReflect", _ -> `KeepOpaque

    | _ when String.prefix ~pre:"Proofs" path
          ||  String.prefix ~pre:"CFML" path
          || String.prefix ~pre:"TLC" path
          || String.prefix ~pre:"Common" path ->
      (* Log.debug (fun f -> f "Expanding %s:%s" path label); *)
      `Unfold
    | _ -> failwith ("UNKNOWN PATH " ^ path ^ " for " ^ "label") in
  let env = Proof_context.env t in
  let (evd, reduced) =
    let evd = Evd.from_env env in
    Proof_reduction.reduce ~filter(* :(fun ~path ~label ->
                                   * Log.debug (fun f -> f "Considering %s:%s -> UNFOLD" path label);
                                   * `Unfold) *)
      env evd (Evd.MiniEConstr.of_constr term) in
  let trm = (EConstr.to_constr evd reduced) in
  let f_app = Proof_utils.extract_trm_app trm in
  Log.info (fun f -> f "initial reduction phase passed @.");
  Configuration.dump_output "reduced-first-try"
    (fun f -> f "%s" (Proof_utils.Debug.constr_to_string trm));
  Configuration.dump_output "reduced-first-try-pretty"
    (fun f -> f "%s" (Proof_utils.Debug.constr_to_string_pretty trm));
  match f_app with
  (* when we fail to reduce the term to an application of a constant wp function, then we have to force the evaluation *)
  | Some f_app when not (Proof_utils.CFML.is_const_wp_fn f_app) ->
    Log.info (fun f -> f "Reduction did not complete - entering phase 2 %s@."
                         (Names.Constant.to_string f_app));
    Gc.full_major ();
    let (evd, reduced) =
      Proof_reduction.reduce
        ~unfold:([f_app])
        ~filter
        env evd (Evd.MiniEConstr.of_constr term) in
    let term = EConstr.to_constr evd reduced in
    Configuration.dump_output "reduced"
      (fun f -> f "%s" (Proof_utils.Debug.constr_to_string term));
    Configuration.dump_output "reduced-pretty"
      (fun f -> f "%s" (Proof_utils.Debug.constr_to_string_pretty term));
    term
  | _ -> trm



(** [build_testing_function t env ?combinator_ty ~pre ~f ~args ~logic_args obs]
    builds a test specification from a partially reduced proof term of
    the lemma [f] applied to values of its arguments [args] at the
    current position in a concrete observation [obs]. [combinator_ty]
    is an optional explicit type if the combinator is one of the
    sisyphus dedicated loop combinators that requires its first
    argument is an explicit type. *)
let build_testing_function t env ?combinator_ty
      ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args ~logic_args:l_args (concrete_args, observations) =
  Log.debug (fun f -> f "build_testing_function called on %s.\nProof context:\n%s"
                        (Names.Constant.to_string lemma_name)
                        (Proof_context.extract_proof_script t));
  Log.debug (fun f -> f "logical params are: %s" ([%show: string list] l_args));
  let higher_order_functions =
    List.combine env.Proof_env.args concrete_args
    |> List.filter_map (function
      | ((f, Lang.Type.Func _), arg) -> Some (f, arg)
      | _ -> None
    ) in

  let test_f =
    List.find_map Option.(fun obs ->
      let obs = Proof_env.normalize_observation env obs in
      Log.debug (fun f -> f "considering observation obs: %s" (show_obs obs));
      Proof_context.with_temporary_context t begin fun () ->
        Log.debug (fun f ->
          f "initial args=%s@."
            ([%show: (Lang.Expr.t * Lang.Type.t) List.t] f_args));
        (* first, instantiate the concrete arguments using values from the trace *)
        let* instantiated_params = instantiate_arguments t env f_args obs in
        Log.debug (fun f ->
          f "instantiated args=%s@."
            ([%show: (Lang.Expr.t * Lang.Type.t) List.t] instantiated_params));

        let params = Option.to_list combinator_ty @ List.map (fun (vl, ty) -> `Typed (vl, ty)) instantiated_params in

        (* next, add evars for the remaining arguments to lemma *)
        let lemma_complete_params, inv_ty =
          build_complete_params t env obs ~inv:inv_ty lemma_name params l_args in

        Log.debug (fun f ->
          f "considering app (%s %s)@."
            (Names.Constant.to_string lemma_name)
            (arg_list_to_str (lemma_complete_params)));

        (* construct term to represent full application of lemma parameters *)
        let trm =
          Format.ksprintf ~f:(Proof_context.term_of t) "%s %s"
            (Names.Constant.to_string lemma_name)
            (arg_list_to_str (lemma_complete_params)) in

        let lambda_env = env.Proof_env.lambda in
        (* partially evaluate/reduce the proof term *)
        let reduced = reduce_term t trm in
        Log.info (fun f -> f "reduction complete!@.");
        (* construct a evaluatable test specification for the invariant *)
        let testf =
          let coq_env = Proof_context.env t in
          let inv_spec = Pair.map String.lowercase_ascii (List.map fst) inv_ty in
          Proof_analysis.analyse coq_env lambda_env higher_order_functions obs pre_heap inv_spec reduced in
        Some testf
      end
    ) observations
    |> Option.get_exn_or "failed to construct an executable test specification" in
  test_f t.Proof_context.compilation_context

let generate_candidate_invariants t env ~mut_vars ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args ~ret:ret_ty observations =
  let uses_options =
    (StringMap.values env.Proof_env.gamma) 
    |> (match ret_ty with None -> Fun.id | Some ty -> Iter.cons ty)
    |> Iter.cons (env.Proof_env.ret_ty)
    |> Iter.exists (Lang.Type.exists (function Lang.Type.ADT ("option", _, _) -> true | _ -> false)) in
  let inv_uses_options =
    (List.to_iter (snd inv_ty) |> Iter.map snd)
    |> Iter.exists (Lang.Type.exists (function Lang.Type.ADT ("option", _, _) -> true | _ -> false)) in

  let uses_option_pair =
    (StringMap.values env.Proof_env.gamma)
    |> (match ret_ty with None -> Fun.id | Some ty -> Iter.cons ty)
    |> Iter.cons (env.Proof_env.ret_ty)
    |> Iter.exists
         (Lang.Type.exists (function Lang.Type.(ADT ("option", [Product [_; _]], _)) -> true | _ -> false)) in
  let inv_uses_option_pair =
    (List.to_iter (snd inv_ty) |> Iter.map snd)
    |> Iter.exists (Lang.Type.exists (function Lang.Type.ADT ("option", [Product [_; _]], _) -> true | _ -> false)) in

  let invariant_has_bool = List.to_iter (snd inv_ty)
                           |> Iter.exists (function (_, Lang.Type.Bool) -> true | _ -> false) in

  let product_types =
    let module TypeSet = Set.Make(struct
                           type t = (Lang.Type.t * Lang.Type.t)
                           [@@deriving ord]
                         end) in
    let types ts ty =
      Lang.Type.fold (fun ts -> function
        | Lang.Type.Product [t1;t2] -> TypeSet.add (t1,t2) ts
        | _ -> ts
      ) ts ty in
    let types =
      (StringMap.values env.Proof_env.gamma)
      |> (match ret_ty with None -> Fun.id | Some ty -> Iter.cons ty)
      |> Iter.cons (env.Proof_env.ret_ty)
      |> Iter.fold types TypeSet.empty in
    TypeSet.to_list types in

  let is_loop_combinator =
    let mod_name = lemma_name |> Names.Constant.modpath |> Names.ModPath.to_string in
    match mod_name with
    | "Common.Verify_combinators" -> true
    | _ -> false in

  (* we'll keep of any logical functions we map to real OCaml functions:  *)
  let hof_rev_map = ref StringMap.empty in
  (* construct an expression generation context using the old proof *)
  let ctx =
    let vars, funcs =
      (* collect all variables in the proof context that are available in the concrete context *)
      let proof_vars =
        let available_vars =
          List.find_map (fun obs ->
            let (pure, _) = Proof_env.normalize_observation env obs in
            Some (List.map fst pure |> StringSet.of_list)
          ) observations
          |> Option.get_or ~default:StringSet.empty in
        let poly_vars, proof_env = Proof_utils.CFML.extract_env (Proof_context.current_goal t).hyp in
        List.filter_map (fun (name, ty) ->
          if StringSet.mem name available_vars
          then Some (name, ty)
          (* handle higher order pure functions:  *)
          else match ty, StringMap.find_opt name env.logical_mappings with
            | Lang.Type.Func (Some _), Some prog_name ->
              (* we need a binding for the function to a corresponding
                 program variable to ensure that the function can be
                 found: *)
              hof_rev_map := StringMap.add prog_name name !hof_rev_map;
              Some (prog_name, ty)
            | Lang.Type.Func (Some _), None ->
              Log.warn (fun f -> f "found usable pure function %s but lacking suitable binding" name);
              None
            | _ -> None
        ) proof_env in
      (* collect any variables that will be available to the invariant *)
      let invariant_vars = snd inv_ty in
      (* variables available to the generation are variables in the proof and from the invariant *)
      let vars = proof_vars @ invariant_vars in
      (* collect functions used in the current proof context *)
      let funcs =
        (* generate initial function set from functions in the hypothesis *)
        Proof_utils.CFML.extract_assumptions (Proof_context.current_goal t).hyp
        |> List.fold_left (fun fns (ty,l,r) ->
          Lang.Expr.(functions (functions fns l) r)
        ) StringSet.empty
        (* add in + and - for  basic arithmetic operations *)
        |> StringSet.add "+"
        |> StringSet.add "-"
        |> (if invariant_has_bool
            then StringSet.add "not"
            else Fun.id)
        |> (if uses_options || inv_uses_options
            then StringSet.add "is_some"
            else Fun.id)
        |> (if inv_uses_options
            then StringSet.add "opt_of_bool"
            else Fun.id)
        |> (if uses_option_pair || inv_uses_option_pair
            then StringSet.add "option_value_fst"
            else Fun.id)
        |> (if uses_option_pair || inv_uses_option_pair
            then StringSet.add "option_value_snd"
            else Fun.id)
        (* add in any hof functions in our proof env  *)
        |> Fun.flip StringSet.add_iter
             (List.to_iter proof_vars
              |> Iter.filter_map (function (name, Lang.Type.Func (Some _)) -> Some name | _ -> None))

        (* add in any logical functions found in the proof *)
        |> Fun.flip StringSet.add_list env.Proof_env.logical_functions

        |> StringSet.to_list in
      vars,funcs in
    let from_id, to_id =
      Dynamic.Matcher.find_aligned_range `Right t.Proof_context.alignment
        ((((t.Proof_context.current_program_id :> int) - 1)),
         (((t.Proof_context.current_program_id :> int)))) in

    Log.debug (fun f ->
      f ~header:"gen-cand-invariants" "%d, %d --> from_id: %d, to_id: %d@."
        (((t.Proof_context.current_program_id :> int) - 1))
        (((t.Proof_context.current_program_id :> int)))
        from_id to_id);

    let initial_values =
      List.concat_map Proof_spec.Heap.Heaplet.(fun (PointsTo (v, _, _) as heaplet) ->
        match heaplet, StringMap.find_opt v env.gamma with
        | PointsTo (_, _, `App ("CFML.Stdlib.Pervasives_proof.Ref", [vl])), Some Lang.Type.(Ref ty)
          when expr_contains_free_variables vl  ->
          [ vl, Lang.Type.to_coq_form ty ]
        | _ -> [ ]) pre_heap in

    Expr_generator.build_context
      ~constants:initial_values
      ~ints:[1;2]
      ~vars ~funcs
      ~env:(fun f -> typeof ~product_types t env f)
      ~from_id ~to_id
      t.Proof_context.old_proof.Proof_spec.Script.proof in

  Log.info (fun f ->
    f ~header:"gen-cand-invariants" "generation context is %a@." Expr_generator.pp_ctx ctx);

  let gen_pure_spec =
    snd inv_ty
    |> List.filter_map (fun (v, ty) ->
      match ty with
      (* if the heap is empty, then everything is useful *)
      | _ when List.is_empty pre_heap -> Some (v, ty)
      | Lang.Type.Int when is_loop_combinator -> None
      (* we only generate equalities for trivial *)
      | Lang.Type.Var _
      | Lang.Type.Int
      | Lang.Type.Bool
      | Lang.Type.Val -> Some (v,ty)
      (* TODO(KIRAN): HANDLE ADTS *)
      | Lang.Type.ADT ("option", _, _) -> Some (v, ty)
      | _ -> None
    ) in

  let ocaml_name proof_var =
    Option.value ~default:proof_var
      (StringMap.find_opt proof_var env.Proof_env.bindings) in

  let gen_heap_spec =
    List.filter_map
      Proof_spec.Heap.Heaplet.(function
        | PointsTo (arr, _, `App ("CFML.WPArray.Array", [ls]))  ->
          let arr = ocaml_name arr in
          let elt_ty =
            match StringMap.find_opt arr env.gamma with
            | Some (Array elt) -> Lang.Type.to_coq_form elt
            | _ ->
              Format.ksprintf ~f:failwith "failed to retrieve type of heaplet %s" arr in
          (* only attempt to synthesize the expression if it is actually mutated   *)
          if StringSet.mem arr mut_vars
          then Some (arr, Lang.Type.List elt_ty)
          else None
        | PointsTo (v, _, `App (("Ref" | "CFML.Stdlib.Pervasives_proof.Ref"), [vl])) ->
          Log.debug (fun f -> f "gen heap spec type of %s is %a" v (Option.pp Lang.Type.pp) (StringMap.find_opt v env.gamma));
          let v = ocaml_name v in
          let elt_ty =
            match StringMap.find_opt v env.gamma with
            | Some (Ref elt) -> Lang.Type.to_coq_form elt
            | _ ->
              Format.ksprintf ~f:failwith "failed to retrieve type of heaplet %s" v in
          (* only attempt to synthesize the expression if it is actually mutated   *)
          if StringSet.mem v mut_vars
          then Some (v, elt_ty)
          else None
        | v ->
          Format.ksprintf ~f:failwith
            "found unsupported heaplet %a" pp v
      ) pre_heap in

  Log.info (fun f ->
    f "Generation target is:\n - pure: %a\n - heap: %s"
      (List.pp (Pair.pp String.pp Lang.Type.pp)) gen_pure_spec
      ([%show: (string * Lang.Type.t) list] gen_heap_spec)
  );

  let gen ?blacklist ?initial ?(fuel=2) = Expr_generator.generate_expression ?blacklisted_vars:blacklist ?initial ~fuel ctx in
  let pure =
    List.map List.(fun (v, ty) ->
      Seq.map (fun expr -> `App ("=", [`Var v; expr])) (gen ~blacklist:[v] ~fuel:3 ~initial:false ty)
    ) gen_pure_spec in
  let expected_empty_pure = List.is_empty gen_pure_spec in

  let heap = (List.map (fun (var, ty) -> Seq.map (fun expr -> (var, expr)) @@ gen ty) gen_heap_spec)  in
  pure, heap, !hof_rev_map, expected_empty_pure

let prune_candidates_using_testf test_f (pure, heap) =
  let pure =
    List.map
      (Seq.filter_map (fun pure ->
         match test_f (pure, [ ]) with
         | false -> None
         | true ->
           match pure with
           | `App ("=", [`Var _;`Var _]) -> None
           | _ -> Some pure
       )) pure in
  let heap =
    List.map (Seq.filter_map (fun heap ->
      if test_f (`Constructor ("true", []), [heap])
      then Some heap
      else None
    )) heap in
  let start_time = Ptime_clock.now () in
  let (no_pure, pure) = List.map seq_force pure |> List.split in
  if List.exists (fun v -> v <= 0) no_pure then
    Format.ksprintf ~f:failwith "ran out of pure candidates";
  Gc.full_major (); 
  let (no_heap, heap) = List.map seq_force heap |> List.split in
  if List.exists (fun v -> v <= 0) no_heap then
    Format.ksprintf ~f:failwith "ran out of heap candidates";
  Gc.full_major (); 
  let end_time = Ptime_clock.now () in
  Log.info (fun f -> f "Pruned down to [%a] pure and [%a] heap in %a"
                       (List.pp Int.pp) no_pure
                       (List.pp Int.pp) no_heap
                       Ptime.Span.pp (Ptime.diff end_time start_time));
  pure, heap

let has_pure_specification t =
  let (_f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let (_, post) = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in
    let f_app = Proof_utils.CFML.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  let (params, invariants, _) = Proof_utils.CFML.extract_spec raw_spec in
  List.for_all (fun (name, invariant) ->
    let _, _, spec =
      Proof_utils.CFML.extract_spec invariant in
    if not (Constr.isApp spec) || not @@ Proof_utils.is_const_eq "CFML.SepLifted.Triple" (fst (Constr.destApp spec)) then
      Format.ksprintf ~f:failwith "unexpected invariant structure, expecting app of triple: %s"
        (Proof_utils.Debug.constr_to_string_pretty spec);
    let[@warning "-8"] [| _; _; _; pre; _ |] = snd (Constr.destApp spec) in
    Proof_utils.CFML.is_hempty pre
  ) invariants


let expr_to_subst t inv_ty expr =
  let expr = Lang.Expr.subst_functions (renormalise_name t) expr in
  let inv_args = (snd inv_ty) |> List.map fst in
  fun args ->
    let binding = StringMap.of_list (List.combine inv_args args) in
    let lookup name = StringMap.find_opt name binding in
    Lang.Expr.subst lookup expr

let expr_to_subst_arr t inv_ty exprs =
  let exprs = Array.map (Lang.Expr.subst_functions (renormalise_name t)) exprs in
  let inv_args = (snd inv_ty) |> List.map fst in
  fun args ->
    let binding = StringMap.of_list (List.combine inv_args args) in
    let lookup name = StringMap.find_opt name binding in
    Array.map (Lang.Expr.subst lookup) exprs


let find_first_valid_candidate_with_z3 t inv_ty vc ~heap ~pure =
  let (let+) x f = Option.bind x f in
  let no_pure = Seq.is_empty pure in
  let heap_gen = Gen.of_seq heap in
  let pure_gen, reset_pure =
    let get_pure () =
      (* if no pure, then just repeatedly return true as the pure *)
      if no_pure
      then (Gen.repeat (`Constructor ("true", [])))
      else (Gen.of_seq pure) in
    let pure_ref = ref (get_pure ()) in
    let pure_gen () = !pure_ref () in
    let reset_pure () = pure_ref := get_pure () in
    pure_gen, reset_pure in

  let should_stop_iteration =
    match Configuration.max_z3_calls () with
    | None -> fun _ -> false
    | Some max_calls -> fun i -> i > max_calls in

  let rec loop i ((pure_candidate, pure_candidate_vc), (heap_candidate, heap_candidate_vc)) =
    Log.info (fun f ->
      f "[%d] testing@.\tPURE:%s@.\tHEAP:%s@." i
        (Format.to_string Lang.Expr.pp (pure_candidate) |> String.replace ~sub:"\n" ~by:" ")
        (Format.to_string (List.pp Lang.Expr.pp) (heap_candidate)  |> String.replace ~sub:"\n" ~by:" "));
    match vc (pure_candidate_vc, heap_candidate_vc) with
    | `InvalidPure ->
      let+ pure_candidate = pure_gen () in
      let pure_candidate_vc = expr_to_subst t inv_ty pure_candidate in
      loop (i + 1) ((pure_candidate, pure_candidate_vc), (heap_candidate, heap_candidate_vc))
    | `InvalidSpatial ->
      (* restart the pure generator *)
      reset_pure ();
      let+ pure_candidate = pure_gen () in
      let pure_candidate_vc = expr_to_subst t inv_ty pure_candidate in
      let+ heap_candidate = heap_gen () in
      let heap_candidate_vc = expr_to_subst_arr t inv_ty (Array.of_list heap_candidate) in
      if should_stop_iteration i
      then (
        Log.warn (fun f -> f "failed to find a solution after %d candidates; giving up, assuming that it is correct" i);
        Some (i, (pure_candidate, heap_candidate))
      )
      else loop (i + 1) ((pure_candidate, pure_candidate_vc), (heap_candidate, heap_candidate_vc))
    | `Valid -> Some (i, (pure_candidate, heap_candidate)) in
  let+ pure_candidate = pure_gen () in
  let+ heap_candidate = heap_gen () in
  let pure_candidate_vc = expr_to_subst t inv_ty pure_candidate in
  let heap_candidate_vc = expr_to_subst_arr t inv_ty (Array.of_list heap_candidate) in
  let start_time = Ptime_clock.now () in
  let res = loop 0 ((pure_candidate, pure_candidate_vc), (heap_candidate, heap_candidate_vc)) in
  let end_time = Ptime_clock.now () in
  let no_candidates =
    Option.map fst res
    |> Option.map_or ~default:"NONE" string_of_int in
  Log.info (fun f ->
    f "found a valid candidate in %a (checked %s candidates)@."
      Ptime.Span.pp Ptime.(diff end_time start_time) no_candidates);
  Option.map snd res

(** [is_simple_expression expr] returns [true] if [expr] is a simple
    expression that CFML will not require an xapp to evaluate - i.e
    things like expressions with only arithmetic, equalities or
    variables. *)
let rec is_simple_expression : Lang.Expr.t -> bool = function
  |`Int _
  | `Var _ -> true
  | `Tuple elts -> List.for_all is_simple_expression elts
  | `App (("+" | "-"), [l;r]) ->
    is_simple_expression l && is_simple_expression r
  | `App ("List.length", [arg]) ->
    is_simple_expression arg
  | `Lambda _ |`Constructor _
  | `App _ -> false

let update_env_with_bindings env = function
  | `Var (var, ty) -> Proof_env.add_binding env ~var ~ty
  | `Tuple vars ->
    List.fold_left
      (fun env (var, ty) ->
         Proof_env.add_binding env ~var ~ty)
      env vars

let rec symexec (t: Proof_context.t) env (body: Lang.Expr.t Lang.Program.stmt) =
  Log.debug (fun f ->
    f ~header:"symexec" "current program id is %s: %s@."
      (t.Proof_context.current_program_id |>  Lang.Id.show)
      (Lang.Program.show_stmt_line Lang.Expr.print body |> String.replace ~sub:"\n" ~by:" "));
  match body with
  | `LetLambda (name, body, rest) ->
    symexec_lambda t env name body rest
  | `LetExp (pat, rewrite_hint, body, rest) ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    begin match body with
    | `App ("Array.make", [_; _]) ->
      symexec_alloc t env pat rest
    | `App ("ref", [_]) ->
      symexec_ref_alloc t env pat rest
    | `App ("Array.get", [_; _]) ->
      symexec_array_get t env pat rest
    | `App (_, prog_args)
      when List.exists (function
        |`Var v -> Proof_env.is_pure_lambda env v
        | _ -> false
      ) prog_args && (has_pure_specification t) ->
      symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest
    | `App (_, args)
      when List.exists (function
        |`Var v -> Proof_env.has_definition env v (* StringMap.mem v env *)
        | _ -> false
      ) args ->
      symexec_higher_order_fun t env pat rewrite_hint args body rest
    | _ -> symexec_opaque_let t env pat rewrite_hint body rest
    end
  | `Match (prog_expr, cases) ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    symexec_match t env prog_expr cases
  | `EmptyArray ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    Proof_context.append t "xvalemptyarr."
  | `IfThenElse (cond, l, r) ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    symexec_if_then_else t env cond l r
  | `Write _ -> failwith "don't know how to handle write"
  | `Value _ ->
    t.current_program_id <- Lang.Id.incr t.current_program_id;
    Log.debug (fun f -> f "well done CHAMP, you're the best AROUND:\n%s@."(Proof_context.extract_proof_script t));
    Proof_context.append t "xvals.";

    while (Proof_context.current_subproof t).goals |> List.length > 0 do
      Proof_context.append t "{ admit. }";
    done
  | t ->
    Format.ksprintf ~f:failwith
      "todo: implement support for %a constructs"
      (Lang.Program.pp_stmt_line Lang.Expr.print) t
and symexec_lambda t env name body rest =
  Log.debug (fun f -> f "[%s] symexec_lambda %s" (t.Proof_context.current_program_id |>  Lang.Id.show) name);
  let fname = Proof_context.fresh ~base:name t in
  let h_fname = Proof_context.fresh ~base:("H" ^ name) t in
  Proof_context.append t "xletopaque %s %s." fname h_fname;
  let env = Proof_env.add_lambda_def t env name body in
  (* update_program_id_over_lambda t body; *)
  symexec t env rest
and symexec_alloc t env pat rest =
  Log.debug (fun f -> f "[%s] symexec_alloc %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat);
  let prog_arr, arr_ty = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of array.make"
    | `Var (var, ty) -> var, ty in
  let arr = Proof_context.fresh ~base:(prog_arr) t in
  let data = Proof_context.fresh ~base:"data"  t in
  let h_data = Proof_context.fresh ~base:("H" ^ data) t in
  Proof_context.append t "xalloc %s %s %s." arr data h_data;
  let env =
    env
    |> Proof_env.add_proof_binding ~proof_var:arr ~program_var:prog_arr
    |> Proof_env.add_binding ~var:prog_arr ~ty:arr_ty in
  symexec t env rest
and symexec_ref_alloc t env pat rest =
  Log.debug (fun f -> f "[%s] symexec_ref_alloc %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat);
  let prog_ref, ref_ty = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of ref"
    | `Var (var, ty) -> var, ty in
  let ref_name = Proof_context.fresh ~base:(prog_ref) t in
  Proof_context.append t "xref %s." ref_name;
  let env =
    env
    |> Proof_env.add_proof_binding ~proof_var:ref_name ~program_var:prog_ref
    |> Proof_env.add_binding ~var:prog_ref ~ty:ref_ty in
  symexec t env rest
and symexec_array_get t env pat rest =
  Log.debug (fun f -> f "[%s] symexec_array_get %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat);
  Proof_context.append t "xinhab.";
  Proof_context.append t "xapp.";
  Proof_context.append t "{";
  Proof_context.append t "try sis_handle_int_index_prove.";
  while List.length (Proof_context.current_subproof t).goals > 0 do 
    Proof_context.append t "admit.";
  done;
  Proof_context.append t "}";
  symexec t env rest
and symexec_opaque_let t env pat _rewrite_hint body rest =
  Log.debug (fun f -> f "[%s] symexec_opaque_let %a = %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat
                        Lang.Expr.pp body
            );
  let prog_var = match pat with
    | `Tuple _ ->
      failwith (Format.sprintf "TODO: implement handling of let _ = %a expressions" Lang.Expr.pp body)
    | `Var (var, _) -> var in
  if is_simple_expression body
  then begin
    let var = Proof_context.fresh ~base:(prog_var) t in
    let h_var = Proof_context.fresh ~base:("H" ^ var) t in
    Proof_context.append t "xletopaque %s %s."  var h_var;
    let env = Proof_env.add_proof_binding env ~proof_var:var ~program_var:prog_var in
    symexec t env rest
  end else begin
    (* let (pre, post) = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in *)
    (* work out the name of function being called and the spec for it *)
    (* let (_lemma_name, _lemma_full_type) =
     *   (\* extract the proof script name for the function being called *\)
     *   let f_app = Proof_utils.CFML.extract_x_app_fun post in
     *   (\* use Coq's searching functionality to work out the spec for the function *\)
     *   find_spec t f_app in *)
    (* TODO: do something smart here (i.e use the type of lemma full type to work out whether to intro any variables ) *)
    Proof_context.append t "xapp.";
    symexec t env rest
  end
and symexec_match t env prog_expr cases =
  Log.debug (fun f -> f "[%s] symexec_match %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp prog_expr);
  (* emit a case analysis to correspond to the program match    *)
  (* for each subproof, first intro variables using the same names as in the program *)
  let sub_proof_vars =
    List.map (fun (_, args, _) ->
      List.map (fun (base, _) -> Proof_context.fresh ~base t) args
    ) cases in
  let case_intro_strs =
    List.map (String.concat " ") sub_proof_vars
    |> String.concat " | "  in
  (* preserve the equality of the program expression *)
  let eqn_var = Proof_context.fresh ~base:("H_eqn") t in
  (* emit a case analysis: *)
  Proof_context.append t "case %a as [%s] eqn:%s."
    Proof_utils.Printer.pp_expr prog_expr case_intro_strs eqn_var;
  (* now, handle all of the sub proofs *)
  List.iter (fun ((_, args, rest), proof_args) ->
    (* start each subproof with an xmatch to determine the appropriate branch *)
    Proof_context.append t "- xmatch.";
    (* update env with bindings for each of the new program vars *)
    let env =
      List.fold_left (fun env ((program_var, _), proof_var) ->
        Proof_env.add_proof_binding env ~proof_var ~program_var
      ) env (List.combine args proof_args) in

    (*  update the proof env with bindings from the match *)
    let env = List.fold_left (fun env (var,ty) ->
      Proof_env.add_binding env ~var ~ty
    ) env args in

    (* now emit the rest *)
    symexec t env rest;
    (* dispatch remaining subgoals by the best method: *)
    while (Proof_context.current_subproof t).goals |> List.length > 0 do
      Proof_context.append t "{ admit. }";
    done;
  ) (List.combine cases sub_proof_vars)
and symexec_if_then_else t env cond l r =
  Log.debug (fun f -> f "[%s] symexec_if_then_else %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp cond);
  Log.debug (fun f -> f "proof script is %s" (Proof_context.extract_proof_script t));
  (* use Kiran's xif as tactic to dispatch the proofs with IMPUNITY *)
  (* come up with a fresh variable to track the value of the conditional in each branch:  *)
  let cond_vl_var = Proof_context.fresh ~base:("H_cond") t in

  Proof_context.append t "xif as %s." cond_vl_var;
  (* now handle if true case *)
  Proof_context.append t "- ";
  symexec t env l;

  Log.debug (fun f ->
    f "subgoals after if true is %d"
      (List.length (Proof_context.current_subproof t).goals)
  );

  (* now handle if else case *)
  Proof_context.append t "- ";
  symexec t env r;

  Log.debug (fun f ->
    f "subgoals after if false is %d"
      (List.length (Proof_context.current_subproof t).goals)
  )

and symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest =
  Log.debug (fun f -> f "[%s] symexec_higher_order_pure_fun %a %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat
                        (List.pp Lang.Expr.pp) prog_args);
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let (_, post) = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in
    let f_app = Proof_utils.CFML.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  Log.debug (fun f -> f "%s" (Proof_utils.Debug.constr_to_string_pretty raw_spec));
  let (params, _invariant, spec) = Proof_utils.CFML.extract_spec raw_spec in

  (* work out the parameters to instantiate *)
  let evar_params =
    params
    (* drop implicits from parameters *)
    |> Proof_utils.drop_implicits f_name
    (* drop concrete arguments *)
    |> List.drop (List.length prog_args)
    (* last parameter is the concretisation of the pure function *)
    |> drop_last in

  (* instantiate evars, and collect variables to clear at end *)
  let clear_vars =
    List.fold_left (fun to_clear (name, _) ->
      let name = Format.to_string Pp.pp_with @@ Names.Name.print name in
      let ty = Proof_context.fresh ~base:("ty_" ^ name ) t in
      Proof_context.append t "evar (%s: Type)." ty;
      let name = Proof_context.fresh ~base:name t in
      Proof_context.append t "evar (%s: %s)." name ty;
      to_clear
      |> List.cons ty
      |> List.cons name
    ) [] evar_params |> List.rev in

  (* emit xapp call *)
  let observation_id, fn_body =
    List.find_map (function
        `Var v -> Proof_env.find_pure_lambda_def env v
      (* StringMap.find_opt v env |> Option.flat_map (Option.if_ Program_utils.is_pure) *)
      | _ -> None) prog_args
    |> Option.get_exn_or "invalid assumptions" in

  Proof_context.append t "xapp (%s %s %s %s)."
    (Names.Constant.to_string f_name)
    (List.map (Proof_utils.Printer.show_expr) prog_args |> String.concat " ")
    (List.map (fun (name, _) -> "?" ^ Format.to_string Pp.pp_with (Names.Name.print name))
       evar_params
     |> String.concat " ")
    (Proof_utils.Printer.show_lambda fn_body);

  (* solve immediate subgoal of xapp automatically. *)
  Proof_context.append t "sep_solve.";

  Log.debug (fun f -> f "proof script:\n%s" (Proof_context.extract_proof_script t));
  (* TODO: repeat based on goal shape, not no goals   *)
  (* any remaining subgoals we assume we can dispatch automatically by eauto. *)
  while List.length (Proof_context.current_subproof t).goals > 1 do
    Proof_context.append t "eauto.";
  done;

  (* finally, clear any evars we introduced at the start  *)
  Proof_context.append t "clear %s." (String.concat " " clear_vars);

  (* destructuring of arguments *)
  let env =
    begin
      match pat with
      | `Var (res_name, res_ty) -> env
      | `Tuple vars ->
        (* if we have a tuple, then we need to do some extra work *)
        let env, vars = List.fold_map (fun env (program_var, _) ->
          let proof_var = Proof_context.fresh ~base:program_var t in
          let env = Proof_env.add_proof_binding env ~proof_var ~program_var in
          env, proof_var
        ) env vars in
        let h_var = Proof_context.fresh ~base:("H" ^ String.concat "" vars) t in
        (* first, emit a xdestruct to split the tuple output - [hvar] remembers the equality *)
        Proof_context.append t "xdestruct %s %s." (String.concat " " vars) h_var;
        (* next, use a user-provided rewrite hint to simplify the equality  *)
        begin match rewrite_hint with
        | Some rewrite_hint ->
          Proof_context.append t "rewrite %s in %s." rewrite_hint h_var;
        | None ->
          failwith "tuple destructuring with functions requires a rewrite hint."
        end;
        (* finally, split the simplified equality on tuples into an equality on terms  *)
        let split_vars = List.map (fun var -> Proof_context.fresh ~base:("H" ^ var) t) vars in
        Proof_context.append t "injection %s; intros %s."
          h_var (String.concat " " @@ List.rev split_vars);
        env
    end in
  (* update program gamma with bindings from result *)
  let env = update_env_with_bindings env pat in
  symexec t env rest
and symexec_higher_order_fun t env pat rewrite_hint prog_args body rest =
  Log.debug (fun f -> f "[%s] symexec_higher_order_fun %a %a"
                        (t.Proof_context.current_program_id |>  Lang.Id.show)
                        Lang.Expr.pp_typed_param pat
                        (List.pp Lang.Expr.pp) prog_args);

  let ret_ty = match pat with
    | `Tuple tys -> Some (Lang.Type.Product (List.map snd tys))
    | `Var (_, Lang.Type.Unit) -> None
    | `Var (_, ty) -> Some (ty) in

  Log.debug (fun f -> f "current proof script is %s" (Proof_context.extract_proof_script t));
  let module PDB = Proof_utils.Debug in
  let (pre, post) = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in
  (* work out the name of function being called and the spec for it *)
  let (lemma_name, lemma_full_type) =
    (* extract the proof script name for the function being called *)
    let f_app = Proof_utils.CFML.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  (* extract the arguments applied to the function call *)
  let (_, f_args) = Proof_utils.CFML.extract_app_full post in

  (* for now we only handle lemmas with a single higher order invariant *)
  let logical_params = ensure_single_invariant ~name:lemma_name ~ty:lemma_full_type ~args:f_args in

  let pre_heap =
    List.filter_map
      (function `Impure heaplet -> Some (Proof_utils.CFML.extract_impure_heaplet heaplet) | _ -> None)
      (match pre with | `Empty -> [] | `NonEmpty ls -> ls) in

  let framed_heaplets, combinator_ty, inv_ty = calculate_inv_ty t ~f:lemma_name ~args:f_args in

  (* collect an observation for the current program point *)
  let observations =
    let cp = t.Proof_context.concrete () in
    let concrete_args = Dynamic.Concrete.args cp in
    let observations = Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in
    concrete_args, observations in

  (* build an initial test specification from the partially reduced proof term applied to values at the current position *)
  let test_f =
    build_testing_function t env ?combinator_ty ~inv:inv_ty ~pre:pre_heap ~f:lemma_name
      ~args:f_args ~logic_args:logical_params observations in

  (* retrieve the body of the higher order function being called *)
  let fun_body =
    List.find_map (function
      | `Var v -> StringMap.find_opt v env.Proof_env.lambda
      | _ -> None) prog_args
    |> Option.map snd
    |> Option.get_exn_or "could not find function definition" in

  (* extract vars mutated by HOF *)
  let mut_vars = Program_utils.mutated_vars fun_body in

  Log.debug (fun f -> f "pre-heap is [%a]" (List.pp Proof_spec.Heap.Heaplet.pp) pre_heap);
  Log.debug (fun f -> f "mutable variables are %a" (StringSet.pp String.pp) mut_vars);

  (* generate initial invariants *)
  let pure, heap, hf_rev_map, expected_no_pure =
    generate_candidate_invariants t env ~mut_vars
      ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args ~ret:ret_ty (snd observations) in

  (* if Configuration.dump_generated_invariants () then begin
   *   Configuration.dump_output "generated-pure-invariants" (fun f ->
   *     f "%a" (Seq.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n@.") Lang.Expr.pp) pure
   *   );
   *   Configuration.dump_output "generated-heap-invariants" (fun f ->
   *     f "%a" (Seq.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n@.") (List.pp Lang.Expr.pp)) heap
   *   );
   * end; *)

  (* prune the candidates using the testing function *)
  let (pure,heap) = prune_candidates_using_testf test_f (pure,heap) in

  (* do it again *)
  let (pure,heap) =
    let test_f =
      let cp = t.Proof_context.concrete () in
      let observations = Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in
      let concrete_args = Dynamic.Concrete.args cp in
      build_testing_function t env ?combinator_ty ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args ~logic_args:logical_params
        (concrete_args, observations) in
    prune_candidates_using_testf test_f (pure,heap) in

  (* and again (50 ms) *)
  let (pure,heap) =
    let test_f =
      let cp = t.Proof_context.concrete () in
      let observations = Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in
      let concrete_args = Dynamic.Concrete.args cp in
      build_testing_function t env ?combinator_ty  ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args
        ~logic_args:logical_params (concrete_args, observations) in
    prune_candidates_using_testf test_f (pure,heap) in


  List.iteri (fun i expr ->
    Log.info (fun f ->
      f "example pure candidate %d: %s@." i ([%show: Lang.Expr.t option list] expr)
    )) [(List.map Seq.head pure)];

  List.iteri (fun i expr -> Log.info  (fun f ->
    f "example heap candidate %d: %s@." i ([%show: (string * Lang.Expr.t) option list] expr)))
    [List.map Seq.head heap];

  (* we check if we found any pure constraints - it may sometimes be
     the case that no pure constraints are needed *)
  let no_pure = List.exists Seq.is_empty pure || List.is_empty pure in

  if no_pure && not expected_no_pure then
    Format.ksprintf ~f:failwith "failed to find pure invariant candidates.";

  let valid_candidate =
    if Configuration.validate_with_z3 () || Option.is_some (Configuration.max_z3_calls ())
    then begin
      (* build a verification condition *)
      let vc =
        let vc =
          Specification.build_verification_condition
            t (Proof_env.env_to_defmap env) lemma_name in
        Configuration.dump_output "verification-condition" (fun f ->
          f "%a@." Proof_validator.VerificationCondition.pp_verification_condition vc);
        Proof_validator.build_validator vc in
      find_first_valid_candidate_with_z3 t inv_ty vc ~heap:(assert false) ~pure:(assert false)
      |> Option.map (Pair.map_snd (List.map (Pair.make "")))
     end else begin
      Log.warn (fun f ->
        f "validation with Z3 is disabled. Assuming that the first \
           invariant we find is valid. (proof left as an exercise to \
           the reader!)");
      let (let+ ) x f = Option.bind x f in
      let pure = match List.map Seq.head pure |> List.all_some with None -> (`Constructor ("true", [])) | Some h -> Lang.Expr.andb h in
      let+ heap = List.map Seq.head heap |> List.all_some in
      Some (pure, heap)
    end in

  let invariant = Option.get_exn_or "Failed to find suitable candidate" valid_candidate in

  (* now before sending things back to the coq context, we have to
     re-normalise any higher order functions back to their pure models
     - in particular, when doing the synthesis, the expression
       generator and proof term evaluator talk about the *real* function
       [f], while our coq terms should talk about the *logical* function
       model [fp]. See [resources/find_mapi/] for an example of how the
       logical model looks. *)
  let invariant =
    let subst v = StringMap.find_opt v hf_rev_map in
    let subst_expr e = Lang.Expr.subst_var subst e in
    (subst_expr (fst invariant), List.map (Pair.map_snd subst_expr) (snd invariant)) in

  Log.info (fun f -> f "FOUND INVARIANT: %s@." (
    [%show: Lang.Expr.t * (string * Lang.Expr.t) Containers.List.t] invariant
  ));

  (* xapp lemma *)
  begin
    let lemma_name = Names.Constant.to_string lemma_name in
    let const_args = (arg_list_to_str (Option.to_list combinator_ty @ (List.map (fun (v, ty) -> `Untyped v) f_args))) in
    let pp_param =
      List.pp
        ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ")
        (Pair.pp
           ~pp_start:(fun fmt () -> Format.pp_print_string fmt "(")
           ~pp_stop:(fun fmt () -> Format.pp_print_string fmt ")")
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ": ")
           Format.pp_print_string
           Proof_utils.Printer.pp_ty) in
    let heap_mapping = List.map Proof_spec.Heap.Heaplet.(fun (PointsTo (v, _, _) as pts) -> (v, pts)) pre_heap
                       |> StringMap.of_list in
    let heap_state =
      begin
        match snd invariant with
        | [] -> ""
        | heap ->
          (if no_pure then "" else " \\* ") ^
          (List.filter_map (fun (v, expr) -> match StringMap.find v heap_mapping with
             | Proof_spec.Heap.Heaplet.PointsTo (v, _, `App (f, _)) when not (StringSet.mem v framed_heaplets) ->
               Some (Format.sprintf "%s ~> %s %a"
                       v f Proof_utils.Printer.pp_expr expr)
             | Proof_spec.Heap.Heaplet.PointsTo (_, _, `App (_, _)) ->
               None
             | Proof_spec.Heap.Heaplet.PointsTo (_, _, v) ->
               Format.ksprintf ~f:failwith
                 "found unsupported heaplet %a" Lang.Expr.pp v
           ) heap
           |> String.concat " \\* ")
      end in
    if no_pure
    then
      (Log.debug (fun f ->
         f "sending: xapp (%s %s (fun %a =>  %s)). to the proof context@."
           lemma_name
           const_args
           pp_param
           (snd inv_ty)
           heap_state);
       Proof_context.append t
         "xapp (%s %s (fun %a =>  %s))."
         lemma_name
         const_args
         pp_param
         (snd inv_ty)
         heap_state)
    else
      (Log.debug (fun f ->
         f "sending: xapp (%s %s (fun %a => \\[ %a ] %s)). to the proof context@."
           lemma_name
           const_args
           pp_param
           (snd inv_ty)
           Proof_utils.Printer.pp_expr
           (fst invariant)
           heap_state);
       Proof_context.append t
         "xapp (%s %s (fun %a => \\[ %a ] %s))."
         lemma_name
         const_args
         pp_param
         (snd inv_ty)
         Proof_utils.Printer.pp_expr
         (fst invariant)
         heap_state)
  end;

  (* dispatch remaining subgoals by the best method: *)
  while (Proof_context.current_subproof t).goals |> List.length > 1 do
    Proof_context.append t "{ admit. }";
  done;

  Log.debug (fun f ->
    f "pattern was %s@."
      ([%show: Lang.Expr.typed_param] pat));
  begin match pat with
  | `Tuple _ ->
    failwith "tuple results from impure functions not supported"

  | `Var (_, Lang.Type.Unit) ->
    if Constr.isProd (Proof_context.current_goal t).ty then
      Proof_context.append t "intros.";
    Proof_context.append t "xmatch."
  | `Var (result, ty) ->
    if Constr.isProd (Proof_context.current_goal t).ty then begin
      let name = Proof_context.fresh ~base:result t in
      let h_name = Proof_context.fresh ~base:("H" ^ result) t in
      Proof_context.append t "intros %s %s." name h_name;
      if Constr.isProd (Proof_context.current_goal t).ty then
        Proof_context.append t "intros.";
    end;
    match snd invariant with
    | [] -> ()
    | _ ->
      Proof_context.append t "try xdestruct."
  end;
  Log.debug (fun f -> f "proof is %s@." (Proof_context.extract_proof_script t));

  (* update program gamma with bindings from result *)
  let env = update_env_with_bindings env pat in
  symexec t env rest

let find_logical_functions t body =
  Lang.Program.fold Lang.Expr.functions StringSet.empty body
  |> StringSet.filter (String.exists Char.(fun c -> ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')))
  |> begin fun set -> StringSet.fold (fun fn_name acc ->
    let fn_name =
      if String.contains fn_name '.'
      then
        let (modl, fn) = List.hd_tl @@ String.split_on_char '.' fn_name in
        modl ^ "_ml" ^ "." ^ String.concat "." fn
      else fn_name in
    let name = Proof_context.names t fn_name in
    match name with
    | None -> acc
    | Some gref ->
      let search_res = Proof_context.search t [
        true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
        true, Search.(GlobSearchLiteral (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef gref)))
      ] |> List.head_opt in
      match search_res with
      | None -> acc
      | Some (spec_name, _, ty) ->
        Log.debug (fun f -> f "found spec for %s" Proof_utils.Debug.(globref_to_string spec_name));
        let _args, _invs, assn = Proof_utils.CFML.extract_spec ty in
        match Constr.kind_nocast assn with
        | Constr.App (f, args) when Proof_utils.is_const_eq "CFML.SepLifted.Triple" f ->
          let pre_heap = match Proof_utils.CFML.extract_heap args.(3) with | `Empty -> [] | `NonEmpty ls -> ls in
          let _, _, post = Constr.destLambda args.(4) in
          let post_heap = match Proof_utils.CFML.extract_heap post with | `Empty -> [] | `NonEmpty ls -> ls in
          Log.debug (fun f -> f "function set before {%a}" (StringSet.pp String.pp) acc);
          let acc = List.fold_left (fun acc -> function
              `Pure c -> Proof_utils.CFML.cfml_extract_logical_functions ~set:acc c
            | `Impure c -> Proof_utils.CFML.cfml_extract_logical_functions ~set:acc c
          ) acc (pre_heap @ post_heap) in
          acc
        | _ -> acc
  ) set StringSet.empty
  end
  |> StringSet.filter_map (fun f -> String.split_on_char '.' f |> List.last_opt)

let generate ?(logical_mappings=[]) t (prog: Lang.Expr.t Lang.Program.t) =
  Proof_context.append t {|xcf.|};
  let pre, post = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in

  let post_ty =
    let post_tag, post_args = Constr.destApp post in
    if not begin
      String.equal "Wptag"
        (fst (Constr.destConst post_tag)
         |> Names.Constant.label
         |> Names.Label.to_string)
    end then
      Format.ksprintf ~f:failwith
        "unexpected goal post format, expected Wptag, found %s"
        (Proof_utils.Debug.constr_to_string_pretty post);

    let post_ty = Proof_utils.CFML.extract_typ post_args.(1) in
    post_ty in


  (* handle pure preconditions *)
  begin match pre with
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    if no_pure > 0 then begin
      let pat =
        Int.range 1 no_pure
        |> Iter.map (fun i -> "H" ^ Int.to_string i)
        |> Iter.intersperse " "
        |> Iter.concat_str in
      Proof_context.append t "xpullpure %s." pat
    end
  | _ -> ()
  end;
  (* collect logical functions found in the specifications of any functions used in the program body  *)
  let logical_functions = find_logical_functions t prog.body in

  Log.debug (fun f -> f "return type is %a" Lang.Type.pp post_ty);

  symexec t (Proof_env.initial_env
               ~ret_ty:post_ty
               ~logical_mappings
               ~logical_functions:(StringSet.to_list logical_functions)
               prog.args) prog.body;
  Proof_context.append t "Admitted.";
  Proof_context.extract_proof_script t
