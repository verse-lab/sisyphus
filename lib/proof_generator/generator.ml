open Containers

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Generates candidate invariants" "gen"))


module ExprSet = Set.Make(Lang.Expr)

let reduce pure =
  let no_pure_original = List.length pure in
  let pure = ExprSet.of_list pure |> ExprSet.to_list in
  let no_pure_updated = List.length pure in
  Log.debug (fun f -> f "reduced %d -> %d unique@." no_pure_original no_pure_updated);
  pure

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

let show_obs obs = [%show: (string * Dynamic.Concrete.value) list * (string * Dynamic.Concrete.heaplet) list] obs

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name)

let arg_list_to_str args =
  (List.map (function
       `Untyped vl -> "(" ^ Proof_utils.Printer.show_expr vl ^ ")"
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

let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

let rec update_program_id_over_lambda (t: Proof_context.t)
          (`Lambda (_, body): [ `Lambda of Lang.Expr.typed_param list * Lang.Expr.t Lang.Program.stmt ])  =
  let rec loop (body: Lang.Expr.t Lang.Program.stmt) = match body with
    | `Match (_, cases) -> 
      t.current_program_id <- Lang.Id.incr t.current_program_id;
      List.iter (fun (_, _, body) -> loop body) cases
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
      t.current_program_id <- Lang.Id.incr t.current_program_id in
  loop body



(** [build_complete_params t lemma_name init_params] returns a pair
    ([complete_params], [head_ty]) where [complete_params] a list of
    concrete arguments to the specification defined by [lemma_name]. To
    do this, it starts with [init_params] and then updates the proof
    context [t] with fresh existential variables for each remaining
    argument.

    Note: assumes that no subsequent arguments past [init_params] are
    implicit. *)
let build_complete_params t ~inv lemma_name init_params =
  let mk_lemma_instantiated_type params = 
    Format.ksprintf
      "%s %s"
      (Names.Constant.to_string lemma_name)
      (arg_list_to_str (List.map (fun v -> v) params))
      ~f:(Proof_context.typeof t) in
  let inv_name = ref (Some (fst inv)) in
  let inv = ref inv in

  let rec loop params lemma_instantiated_type =
    match Constr.kind lemma_instantiated_type with
    | Prod (Context.{binder_name; _}, ty, _) ->
      let evar_name =
        let base = match binder_name with
          | Names.Name.Anonymous -> None
          | Names.Name.Name _ -> Some (Format.to_string Pp.pp_with @@ Names.Name.print binder_name) in

        let new_name = Proof_context.fresh ?base t in
        (* if we're defining an evar for the env, then we sometimes
           run into problems if the name of the inv in the
           specification happens to be already bound in the context.

           As such, here we have a little check to update the name of
           the invariant type to the name returned by fresh. *)
        begin match !inv_name, base with
        | Some i_name, Some b_name when String.equal i_name b_name ->
          inv_name := None;
          inv := (new_name, snd !inv);
        | _ -> ()
        end;
        new_name in
      Proof_context.append t "evar (%s: %s)." evar_name
        (Proof_utils.Debug.constr_to_string_pretty ty);
      let params = params @ [`Untyped (`Var evar_name)] in
      let lemma_instantiated_type = mk_lemma_instantiated_type params in
      loop params lemma_instantiated_type
    | _ -> params, lemma_instantiated_type in
  let params, _ = loop init_params (mk_lemma_instantiated_type init_params) in
  params, !inv

(** [instantiate_arguments t env args (ctx, heap_ctx)] attempts to
    instantiate a list of concrete arguments [args] using an observed
    context [ctx] and heap state [heap_ctx] from an execution trace.
    To do this, it may introduce additional evars in proof context [t]
    to represent polymorphic values. *)
let instantiate_arguments t env args (ctx, heap_ctx) =
  let lookup_var v ty =
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
  let rec instantiate_expr (vl, ty) =
    match vl, ty with
    | `Var v, ty -> (lookup_var v ty) |> Option.map (fun vl -> (vl, ty))
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
    | expr, ty -> Some (expr, ty) in
  List.map instantiate_expr args
  |> List.all_some

(** [ensure_single_invariant ~name ~ty ~args] when given the
    application of lemma [name] to arguments [args], where [name] has
    type [ty]. *)
let ensure_single_invariant ~name:lemma_name ~ty:lemma_full_type ~args:f_args  =
  let (lemma_params, lemma_invariants, spec) = Proof_utils.CFML.extract_spec lemma_full_type in
  let explicit_lemma_params = Proof_utils.drop_implicits lemma_name lemma_params in
  let param_bindings, remaining = combine_rem explicit_lemma_params f_args in
  match remaining with
  | Some (Right _) | None | Some (Left [])  ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with no invariant/insufficient arguments?"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left (_ :: _ :: _)) ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with multiple invariants"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left [_, _]) -> () 

let typeof t (s: string) : (Lang.Type.t list * Lang.Type.t) option =
  let (let+) x f = Option.bind x f in
  let ty = 
    match s with
    | "++" -> Some Lang.Type.([List (Var "A"); List (Var "A")], List (Var "A"))
    | "-" -> Some Lang.Type.([Int; Int], Int)
    | "+" -> Some Lang.Type.([Int; Int], Int)
    | s ->
      try 
        let ty = (Proof_context.typeof t s) in
        let+ s_base = String.split_on_char '.' s |> List.last_opt in
        let+ name = Proof_context.names t s_base in
        match name with
        | Names.GlobRef.ConstRef s ->
          let Lang.Type.Forall (poly, args) = Proof_utils.CFML.extract_fun_typ s ty in
          Some (split_last args)
        | _ -> None
      with
      | _ -> None in
  (* Log.debug (fun f -> f "checking the type of %s -> %s\n@." s ([%show: (Lang.Type.t list * Lang.Type.t) Containers.Option.t] ty)); *)
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

let calculate_inv_ty t ~f:lemma_name ~args:f_args =
  let instantiated_spec =
    Format.sprintf "%s %s" (Names.Constant.to_string lemma_name)
      (arg_list_to_str (List.map (fun (v, ty) -> `Typed (v, ty)) f_args)) in
  let instantiated_spec = (Proof_context.typeof t instantiated_spec) in
  let (Context.{binder_name; _}, ty, rest) = Constr.destProd instantiated_spec in
  let tys = Proof_utils.CFML.unwrap_invariant_type ty in
  let tys = List.mapi (fun i v -> Format.sprintf "arg%d" i, v) tys in
  name_to_string binder_name, tys 

(** [reduce_term t term] reduces a proof term [term] using ultimate
    reduction.  *)
let reduce_term t term =
  let filter ~path ~label =
    match path with
    (* | "Coq.Init.Logic.eq_ind" when Option.is_some !eq_ind_reduce_name ->
     *   `Subst (fst @@ Option.get_exn_or "invalid assumptions" !eq_ind_reduce_name) *)
    | "Coq.ZArith.BinInt.Z"
    | "Coq.ZArith.Znat.Nat2Z"
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
      -> `KeepOpaque

    | _ when String.prefix ~pre:"Proofs" path
          ||  String.prefix ~pre:"CFML" path
          || String.prefix ~pre:"TLC" path -> `Unfold
    | _ -> failwith ("UNKNOWN PATH " ^ path) in
  let env = Proof_context.env t in
  let (evd, reduced) =
    let evd = Evd.from_env env in
    Proof_reduction.reduce ~filter:(fun ~path ~label -> `Unfold)
      env evd (Evd.MiniEConstr.of_constr term) in
  let trm = (EConstr.to_constr evd reduced) in
  let f_app = Proof_utils.extract_trm_app trm in
  Log.info (fun f -> f "initial reduction phase passed @.");
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



(** [build_testing_function t env ~pre ~f ~args obs] builds a test
    specification from a partially reduced proof term of the lemma [f]
    applied to values of its arguments [args] at the current position
    in a concrete observation [obs] *)
let build_testing_function t env ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations =
  Log.debug (fun f -> f "build_testing_function called on %s.\nProof context:\n%s"
                        (Names.Constant.to_string lemma_name)
                        (Proof_context.extract_proof_script t));
  let test_f =
    List.find_map Option.(fun obs ->
      let obs = Proof_env.normalize_observation env obs in
      Proof_context.with_temporary_context t begin fun () ->
        Log.debug (fun f ->
          f "initial args=%s@."
            ([%show: (Lang.Expr.t * Lang.Type.t) List.t] f_args));
        (* first, instantiate the concrete arguments using values from the trace *)
        let* instantiated_params = instantiate_arguments t env f_args obs in
        Log.debug (fun f ->
          f "instantiated args=%s@."
            ([%show: (Lang.Expr.t * Lang.Type.t) List.t] instantiated_params));

        (* next, add evars for the remaining arguments to lemma *)
        let lemma_complete_params, inv_ty =
          build_complete_params t ~inv:inv_ty lemma_name (List.map (fun (vl, ty) -> `Typed (vl, ty)) instantiated_params) in

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
          Proof_analysis.analyse coq_env lambda_env obs inv_spec reduced in
        Some testf
      end
    ) observations
    |> Option.get_exn_or "failed to construct an executable test specification" in
  test_f t.Proof_context.compilation_context 

let generate_candidate_invariants t env ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations =
  (* construct an expression generation context using the old proof *)
  let ctx =
    let vars, funcs =
      (* collect all variables in the proof context that are available in the concrete context *)
      let proof_vars =
        let available_vars =
          List.find_map (fun obs ->
            let (pure, _) = Proof_env.normalize_observation env obs in
            Some (List.map fst pure |> StringSet.of_list)
          ) observations |> Option.get_or ~default:StringSet.empty in
        let poly_vars, env = Proof_utils.CFML.extract_env (Proof_context.current_goal t).hyp in
        List.filter (Pair.fst_map (Fun.flip StringSet.mem available_vars)) env in
      (* collect any variables that will be available to the invariant *)
      let invariant_vars = snd inv_ty in
      (* variables available to the generation are variables in the proof and from the invariant *)
      let vars = proof_vars @ invariant_vars in
      (* collect functions used in the current proof context *)
      let funcs =
        Proof_utils.CFML.extract_assumptions (Proof_context.current_goal t).hyp
        |> List.fold_left (fun fns (ty,l,r) ->
          Lang.Expr.(functions (functions fns l) r)
        ) StringSet.empty
        |> StringSet.add "+"
        |> StringSet.add "-"
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
    Expr_generator.build_context ~ints:[1;2]
      ~vars ~funcs ~env:(typeof t)
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
      (* we only generate equalities for trivial *)
      | Lang.Type.Var _
      | Lang.Type.Int
      | Lang.Type.Val -> Some (v,ty)
      | _ -> None
    ) in
  let gen_heap_spec =
    List.map
      Proof_spec.Heap.Heaplet.(function
          PointsTo (v, _, `App ("CFML.WPArray.Array", _)) ->
          Lang.Type.List (Lang.Type.Var "A")
        | PointsTo (v, _, `App ("Ref", _)) ->
          Lang.Type.Var "A"
        | v ->
          Format.ksprintf ~f:failwith
            "found unsupported heaplet %a" pp v
      ) pre_heap in

  let gen ?blacklist ?initial ?(fuel=2) = Expr_generator.generate_expression ?blacklisted_vars:blacklist ?initial ~fuel ctx (typeof t) in
  let pure =
    List.map_product_l List.(fun (v, ty) ->
      List.map (fun expr -> `App ("=", [`Var v; expr])) (gen ~blacklist:[v] ~fuel:3 ~initial:false ty)
    ) gen_pure_spec
    |> List.filter_map (function
        [] -> None
      | h :: t ->
        List.fold_left
          (fun acc vl -> `App ("&&", [vl; acc])) h t
        |> Option.some
    ) in
  let heap = List.map_product_l (gen) gen_heap_spec in
  pure, heap

let prune_candidates_using_testf test_f (pure, heap) =
  let start_time = Ptime_clock.now () in
  let pure = 
    List.filter_map (fun pure ->
      match test_f (pure, [ ]) with 
      | false -> None
      | true ->
        match pure with
        | `App ("=", [`Var _;`Var _]) -> None
        | _ ->
          Some pure
    ) pure in
  let heap =
    List.filter_map (fun heap ->
      if test_f (`Constructor ("true", []), heap)
      then Some heap
      else None
    ) heap in
  let end_time = Ptime_clock.now () in
  let no_pure = (List.length pure) in
  let no_impure = (List.length heap) in
  Log.info (fun f ->
    f "pruned down to %d pure candidates and %d heap candidates in %a @."
      no_pure
      no_impure
      Ptime.Span.pp
      (Ptime.diff end_time start_time));
  if no_pure < 10 then
    Log.debug (fun f -> f "pure candidates: %s@." ([%show: Lang.Expr.t Containers.List.t] pure));
  if no_impure < 10 then
    Log.debug (fun f -> f "heap candidates: %s@." ([%show: Lang.Expr.t list list] heap));

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
  let no_pure = List.is_empty pure in
  let heap_gen = Gen.of_list heap in
  let pure_gen, reset_pure = 
    let get_pure () =
      (* if no pure, then just repeatedly return true as the pure *)
      if no_pure
      then (Gen.repeat (`Constructor ("true", [])))
      else (Gen.of_list pure) in
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
  | `Write _ -> failwith "don't know how to handle write"
  | `Value _ ->
    Proof_context.append t "xvals.";

    while (Proof_context.current_subproof t).goals |> List.length > 0 do 
      Proof_context.append t "{ admit. }";
    done
and symexec_lambda t env name body rest =
  let fname = Proof_context.fresh ~base:name t in
  let h_fname = Proof_context.fresh ~base:("H" ^ name) t in
  Proof_context.append t "xletopaque %s %s." fname h_fname;
  let env = Proof_env.add_lambda_def t env name body in
  (* update_program_id_over_lambda t body; *)
  symexec t env rest
and symexec_alloc t env pat rest =
  let prog_arr = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of array.make"
    | `Var (var, _) -> var in
  let arr = Proof_context.fresh ~base:(prog_arr) t in
  let data = Proof_context.fresh ~base:"data"  t in
  let h_data = Proof_context.fresh ~base:("H" ^ data) t in
  Proof_context.append t "xalloc %s %s %s." arr data h_data;
  let env = Proof_env.add_proof_binding env ~proof_var:arr ~program_var:prog_arr in
  symexec t env rest
and symexec_opaque_let t env pat _rewrite_hint body rest =
  let prog_var = match pat with
    | `Tuple _ ->
      failwith (Format.sprintf "TODO: implement handling of let _ = %a expressions" Lang.Expr.pp body)
    | `Var (var, _) -> var in
  let var = Proof_context.fresh ~base:(prog_var) t in
  let h_var = Proof_context.fresh ~base:("H" ^ var) t in
  Proof_context.append t "xletopaque %s %s."  var h_var;
  let env = Proof_env.add_proof_binding env ~proof_var:var ~program_var:prog_var in
  symexec t env rest
and symexec_match t env prog_expr cases =
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
    (* now emit the rest *)
    symexec t env rest;
    (* dispatch remaining subgoals by the best method: *)
    while (Proof_context.current_subproof t).goals |> List.length > 0 do 
      Proof_context.append t "{ admit. }";
    done;
  ) (List.combine cases sub_proof_vars)
and symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest =
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
        `Var v -> Proof_env.find_pure_lambda_def env v (* StringMap.find_opt v env |> Option.flat_map (Option.if_ Program_utils.is_pure) *)
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
  begin
    match pat with
    | `Var _ -> ()
    | `Tuple vars ->
      (* if we have a tuple, then we need to do some extra work *)
      let vars = List.map (fun (name, _) ->
        Proof_context.fresh ~base:name t
      ) vars in
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
  end;
  symexec t env rest
and symexec_higher_order_fun t env pat rewrite_hint prog_args body rest =
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
  ensure_single_invariant ~name:lemma_name ~ty:lemma_full_type ~args:f_args;

  let pre_heap = 
    List.filter_map
      (function `Impure heaplet -> Some (Proof_utils.CFML.extract_impure_heaplet heaplet) | _ -> None)
      (match pre with | `Empty -> [] | `NonEmpty ls -> ls) in

  let inv_ty = calculate_inv_ty t ~f:lemma_name ~args:f_args in


  (* collect an observation for the current program point *)
  let observations =
    let cp = t.Proof_context.concrete () in
    Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in

  (* build an initial test specification from the partially reduced proof term applied to values at the current position *)
  let test_f = build_testing_function t env ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations in

  (* generate initial invariants *)
  let pure, heap = generate_candidate_invariants t env ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations in

  let () =
    let no_pure = List.length pure in
    let no_impure = List.length heap in
    Log.debug (fun f ->
      f "found %d pure candidates and %d heap candidates@." no_pure no_impure;
    );
    if no_pure < 10 then
      Log.debug (fun f -> f "pure candidates: %s@." ([%show: Lang.Expr.t Containers.List.t] pure));
    if no_impure < 10 then
      Log.debug (fun f -> f "heap candidates: %s@." ([%show: Lang.Expr.t list list] heap)) in


  (* prune the candidates using the testing function *)
  let (pure,heap) =
    prune_candidates_using_testf test_f (pure,heap) in

  (* do it again *)
  let (pure,heap) = 
    let test_f =
      let cp = t.Proof_context.concrete () in
      let observations = Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in
      build_testing_function t env ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations in
    prune_candidates_using_testf test_f (pure,heap) in

  (* and again (50 ms) *)
  let (pure,heap) = 
    let test_f =
      let cp = t.Proof_context.concrete () in
      let observations = Dynamic.Concrete.lookup cp ((t.Proof_context.current_program_id :> int) - 1) in
      build_testing_function t env  ~inv:inv_ty ~pre:pre_heap ~f:lemma_name ~args:f_args observations in
    prune_candidates_using_testf test_f (pure,heap) in


  List.iteri (fun i expr -> Log.info (fun f ->
    f "example pure candidate %d: %s@." i ([%show: Lang.Expr.t] expr))) (List.take 1 pure);
  List.iteri (fun i expr -> Log.info  (fun f ->
    f "example heap candidate %d: %s@." i ([%show: Lang.Expr.t list] expr))) (List.take 1 heap);

  (* we check if we found any pure constraints - it may sometimes be
     the case that no pure constraints are needed *)
  let no_pure = List.is_empty pure in

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
      find_first_valid_candidate_with_z3 t inv_ty vc ~heap ~pure
    end
    else begin
      Log.warn (fun f ->
        f "validation with Z3 is disabled. Assuming that the first \
           invariant we find is valid. (proof left as an exercise to \
           the reader!)");
      let (let+ ) x f = Option.bind x f in
      let pure = match pure with [] -> (`Constructor ("true", [])) | h :: _ -> h in
      let+ heap = List.head_opt heap in
      Some (pure, heap)
    end in

  let invariant = Option.get_exn_or "Failed to find suitable candidate" valid_candidate in
  Log.info (fun f -> f "FOUND INVARIANT: %s@." (
    [%show: Lang.Expr.t * Lang.Expr.t Containers.List.t] invariant
  ));

  (* xapp lemma *)
  begin
    let lemma_name = Names.Constant.to_string lemma_name in
    let const_args = (arg_list_to_str (List.map (fun (v, ty) -> `Untyped v) f_args)) in
    let pp_param =
      List.pp
        ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ")
        (Pair.pp
           ~pp_start:(fun fmt () -> Format.pp_print_string fmt "(")
           ~pp_stop:(fun fmt () -> Format.pp_print_string fmt ")")
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ": ")
           Format.pp_print_string
           Proof_utils.Printer.pp_ty) in
    let heap_state =
      begin
        match snd invariant with
        | [] -> ""
        | heap ->
          (if no_pure then "" else " \\* ") ^
          (List.map (function
             | Proof_spec.Heap.Heaplet.PointsTo (v, _, `App (f, _)), expr ->
               Format.sprintf "%s ~> %s %a"
                 v f Proof_utils.Printer.pp_expr expr
             | Proof_spec.Heap.Heaplet.PointsTo (_, _, v), _ -> 
               Format.ksprintf ~f:failwith
                 "found unsupported heaplet %a" Lang.Expr.pp v
           ) (List.combine pre_heap heap)
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
  | `Tuple _ -> failwith "tuple results from not supported"

  | `Var (_, Lang.Type.Unit) ->
    Proof_context.append t "xmatch."

  | `Var (result, _) ->
    let name = Proof_context.fresh ~base:result t in
    let h_name = Proof_context.fresh ~base:("H" ^ result) t in
    Proof_context.append t "intros %s %s." name h_name;
    match snd invariant with
    | [] -> ()
    | _ ->
      Proof_context.append t "try xdestruct."
  end;
  Log.debug (fun f -> f "proof is %s@." (Proof_context.extract_proof_script t));

  symexec t env rest


let generate ?(logical_mappings=[]) t (prog: Lang.Expr.t Lang.Program.t) =
  Proof_context.append t {|xcf.|};
  let pre, _ = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in

  (* handle pure preconditions *)
  begin match pre with
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    let pat = 
      Int.range 1 no_pure
      |> Iter.map (fun i -> "H" ^ Int.to_string i)
      |> Iter.intersperse " "
      |> Iter.concat_str in
    Proof_context.append t "xpullpure %s." pat;
  | _ -> ()
  end;

  symexec t (Proof_env.initial_env ~logical_mappings prog.args) prog.body;
  Proof_context.append t "Admitted.";
  Proof_context.extract_proof_script t

