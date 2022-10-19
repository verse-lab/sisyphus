open Containers
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

module PU = Proof_utils
module PCFML = Proof_utils.CFML
module PV = Proof_validator.VerificationCondition

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Generates Z3 verification conditions" "gen.spec"))

let () =
  Printexc.register_printer (function
      Failure msg -> Some msg
    | _ -> None
  )

let globref_to_string = function
  | Names.GlobRef.VarRef v -> Names.Id.to_string v
  | Names.GlobRef.ConstRef c -> Names.Constant.to_string c
  | Names.GlobRef.IndRef (i, _) -> Names.MutInd.to_string i 
  | Names.GlobRef.ConstructRef ((c, _), _) -> Names.MutInd.to_string c

let rec extract_property acc (c: Constr.t) =
  match Constr.kind_nocast c with
  | Constr.Prod ({binder_name=Name n; _}, ty, c) when Constr.is_Type ty ->
    extract_property (Names.Id.to_string n :: acc) c
  | Constr.Prod (_, _, _) ->
    extract_params acc [] c
  | Constr.App (eq, [| _; _; _ |]) when PU.is_coq_eq eq ->
    extract_conclusion acc [] [] c
  | _ ->
    failwith (Format.sprintf "(extract property) found unsupported assertion %s" (Proof_utils.Debug.constr_to_string_pretty c))
and extract_params tys acc (c: Constr.t) =
  match Constr.kind_nocast c with
  | Constr.Prod ({binder_name=Name n; _}, ty, rest) ->
    let rel ind =
      let ind = ind - 1 in
      if ind < List.length acc
      then List.nth acc ind |> snd
      else List.nth tys (ind - List.length acc) |> (fun v -> Lang.Type.Var v) in
    let n = Names.Id.to_string n in
    let ty = PCFML.extract_typ_opt ~rel ty in
    begin match ty with
    | Some ty -> extract_params tys ((n, ty) :: acc) rest
    | None -> extract_assertions tys acc [] rest
    end
  | _ -> extract_assertions tys acc [] c
and extract_assertions tys params acc (c: Constr.t) =
  let rel ind =
    let ind = ind - 1 in
    if ind < List.length acc then
      failwith (Format.sprintf "(extract assertions) found dependent types");
    let ind = ind - List.length acc in
    if ind < List.length params
    then List.nth params ind |> snd
    else List.nth tys (ind - List.length params) |> (fun v -> Lang.Type.Var v) in
  let rel_exp ind =
    let ind = ind - 1 in
    if ind < List.length acc then
      failwith (Format.sprintf "(extract assertions) found dependent types");
    let ind = ind - List.length acc in
    if ind < List.length params
    then List.nth params ind |> fst
    else failwith "(extract assertions) attempt to index out of bounds" in
  match Constr.kind_nocast c with
  | Constr.Prod (_, exp, c) when Constr.isApp exp && Constr.destApp exp |> fst |> PU.is_coq_eq ->
    let[@warning "-8"] _, [| ty; l; r |] = Constr.destApp exp in
    let ty = PCFML.extract_typ ~rel ty in
    let l = PCFML.extract_expr ~rel:rel_exp l in
    let r = PCFML.extract_expr ~rel:rel_exp r in
    extract_assertions tys params (`Eq (ty, l, r) :: acc) c
  | Constr.Prod (_, exp, c) ->
    let exp = PCFML.extract_expr ~rel:rel_exp exp in
    extract_assertions tys params (`Assert exp :: acc) c
  | Constr.App _ ->
    extract_conclusion tys params acc c
  | _ ->
    failwith (Format.sprintf "(extract assertions) found unsupported assertion %s" (Proof_utils.Debug.constr_to_string_pretty c))
and extract_conclusion tys params assertions (c: Constr.t) =
  let rel ind =
    let ind = ind - 1 in
    if ind < List.length assertions then
      failwith (Format.sprintf "(extract equality) found dependent types");
    let ind = ind - List.length assertions in
    if ind < List.length params
    then List.nth params ind |> snd
    else
      let ind = ind - List.length params in
      if ind < 0 then
        failwith (Format.sprintf "(extract equality) found dependent types");
      List.nth tys ind  |> (fun v -> Lang.Type.Var v) in
  let rel_exp ind =
    let ind = ind - 1 in
    if ind < List.length assertions then
      failwith (Format.sprintf "(extract equality) found dependent types");
    let ind = ind - List.length assertions in
    if ind < List.length params
    then List.nth params ind |> fst
    else failwith (Format.sprintf "(extract equality) attempt to index out of bounds") in
  match Constr.kind_nocast c with
  | Constr.App (fname, [| ty; l; r |]) when PU.is_coq_eq fname ->
    let ty = PCFML.extract_typ ~rel ty in
    let l = PCFML.extract_expr ~rel:rel_exp l in
    let r = PCFML.extract_expr ~rel:rel_exp r in
    (List.rev tys, List.rev params, List.rev assertions, `Eq (ty, l, r))
  | Constr.App (fname, _) when PU.is_const_eq "TLC.LibOrder.le" fname
                             || PU.is_const_eq "TLC.LibOrder.lt" fname
                             || PU.is_const_eq "TLC.LibOrder.ge" fname
                             || PU.is_const_eq "TLC.LibOrder.gt" fname ->
    (List.rev tys, List.rev params, List.rev assertions, `Assert (PCFML.extract_expr ~rel:rel_exp c))
  | _ ->
    failwith (Format.sprintf "(extract equality) found unsupported assertion %s"
                (Proof_utils.Debug.constr_to_string_pretty c))

let extract_property c =
  try Ok (extract_property [] c) with
  | Failure msg ->
    Error (Format.sprintf "failed to parse type %s, due to %s" (Proof_utils.Debug.constr_to_string_pretty c) msg)
  | e -> Error (Printexc.to_string e)

type constr = Constr.t
let pp_constr fmt vl = Format.pp_print_string fmt (Proof_utils.Debug.constr_to_string_pretty vl)
let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

let build_hole_var id = ((Format.sprintf "S__hole_%d" id))

let rec normalize_constr c =
  if Constr.isCast c
  then let c, _, _ = Constr.destCast c in normalize_constr c
  else c

(** [unwrap_invariant_spec formals env hole_binding sym_heap
   no_conditions trm] given an term [trm] that represents the type of
   a specification for a higher order function to a combinator,
   extracts a description of the condition in a form that can be sent
   to Z3. *)
let unwrap_invariant_spec formals
      (env: PV.def_map)
      (hole_binding: int StringMap.t)
      (sym_heap: Proof_spec.Heap.Heap.t) no_conditions (c: Constr.t) =
  let check_or_fail ?(fmt=fun () -> "opaque") name pred v = 
    if pred v then v
    else Format.ksprintf ~f:failwith "failed to find \"%s\" in %s within goal %s" name
           (fmt ())
           (Proof_utils.Debug.constr_to_string_pretty c) in
  let no_formals = List.length formals in
  (* [collect_params] assumes that the named arguments to the higher
     order specification are additional parameters to the invariant,
     and then calls {!collect_assumptions}: *)
  let rec collect_params acc c = 
    let rel ind =
      let ind = ind - 1 in
      let ind = ind - no_conditions in
      let ind = ind - no_formals in
      snd (List.nth acc ind) in
    match Constr.kind_nocast c with
    | Constr.Prod ({binder_name=Name name; _}, ty, rest) ->
      collect_params ((Names.Id.to_string name, Proof_utils.CFML.extract_typ ~rel ty) :: acc) rest
    | Constr.Prod (_, _, _) -> collect_assumptions acc [] c
    | _ -> 
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] in (%s) which was expected \
         to be a invariant spec (forall ..., eqns, SPEC (_), _)"
        (Proof_utils.Debug.constr_to_string c) (Proof_utils.Debug.tag c) (Proof_utils.Debug.constr_to_string_pretty c)
  (* [collect_assumptions params acc c] accumulates the pure side
     conditions of a higher order specification into [acc] and then
     calls {!collect_spec} once it reaches the hoare triple describing
     the invariant. *)
  and collect_assumptions params acc c = 
    match Constr.kind_nocast c with
    | Constr.Prod (_, ty, rest) ->
      let rel ind =
        let ind = ind - 1 in
        let ind = ind - List.length acc in
        fst (List.nth params ind) in
      let assum = PCFML.unwrap_eq ~rel ty in
      collect_assumptions params (assum :: acc) rest
    | Constr.App (fname, _) when PU.is_const_eq "CFML.SepLifted.Triple" fname ->
      collect_spec params acc c
    | _ ->
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] in (%s) which was \
         expected to be a invariant spec. Expecting (eqns, SPEC (_), \
         _)" (Proof_utils.Debug.constr_to_string c) (Proof_utils.Debug.tag c) (Proof_utils.Debug.constr_to_string_pretty c)
  (* [collect_spec params assums trm] *)
  and collect_spec params assums c =
    match Constr.kind_nocast c with
    | Constr.App (fname, [| f_app; _; _; pre; post |]) when PU.is_const_eq "CFML.SepLifted.Triple" fname ->
      let rel ind =
        let ind = ind - 1 in
        let ind = ind - List.length assums in
        fst (List.nth params ind) in

      let f_name, f_args = 
        let f_app, args =
          check_or_fail "app" Constr.isApp f_app
          |> Constr.destApp
          |> check_or_fail "Trm Apps" Fun.(PU.is_const_eq "CFML.SepLifted.Trm_apps" % fst)
          |> snd
          |> fun arr -> (normalize_constr arr.(0), arr.(1)) in
        let f_app =
          check_or_fail ~fmt:(fun () -> PU.Debug.constr_to_string_pretty f_app)
            "var function ref" Constr.isVar f_app
          |> Constr.destVar
          |> Names.Id.to_string in
        let args = PU.unwrap_inductive_list args
                   |> List.to_iter
                   |> Iter.map normalize_constr
                   |> Iter.map (PCFML.extract_dyn_var ~rel)
                   |> Iter.to_list in
        f_app, args in

      let _, init_param_values = 
        let inv, args =
          pre
          |> check_or_fail "pre-condition invariant app" Constr.isApp
          |> Constr.destApp in
        let inv: (string * Lang.Type.t list) =
          inv 
          |> check_or_fail "local invariant" Constr.isRel
          |> Constr.destRel
          |> (fun r -> r - 1)
          |> check_or_fail "reference to local invariant greater than assums" ((<=) List.(length assums))
          |> (fun r -> r - List.length assums)
          |> check_or_fail "reference to local invariant greater than params" ((<=) List.(length params))
          |> (fun r -> r - List.length params)
          |> check_or_fail "reference to local invariant greater than no_conditions" ((<=) no_conditions)
          |> (fun r -> r - no_conditions)
          |> List.nth formals in
        let args = Array.to_iter args |> Iter.map (PCFML.extract_expr ~rel) |> Iter.to_list in
        inv, args in

      let post_name, _, _, post_args = 
        let (name, ty, body) =
          post
          |> check_or_fail "fun post condition" Constr.isLambda
          |> Constr.destLambda in
        let name =
          name
          |> (fun name -> name.binder_name)
          |> check_or_fail "named post return arg" Names.Name.is_name
          |> (function[@warning "-8"] Names.Name.Name name -> Names.Id.to_string name) in
        let ty =
          let rel ind =
            let ind = ind - 1 in
            let ind = ind - List.length assums in
            snd (List.nth params ind) in
          PCFML.extract_typ ~rel ty in
        let rel ind =
          let ind = ind - 1 in
          if ind = 0
          then name
          else let ind = ind - 1 in
            let ind = ind - List.length assums in
            fst (List.nth params ind) in
        let inv, args =
          body
          |> check_or_fail "single invariant application in post" Constr.isApp
          |> Constr.destApp in
        let inv: (string * Lang.Type.t list) =
          inv 
          |> check_or_fail "local invariant" Constr.isRel
          |> Constr.destRel
          |> (fun r -> r - 1)   (* subtract 1 for 1 indexing *)
          |> (fun r -> r - 1)   (* subtract 1 for the fun _ => .. *)
          |> check_or_fail "reference to local invariant greater than assums" ((<=) List.(length assums))
          |> (fun r -> r - List.length assums)
          |> check_or_fail "reference to local invariant greater than params" ((<=) List.(length params))
          |> (fun r -> r - List.length params)
          |> check_or_fail "reference to local invariant greater than no_conditions" ((<=) no_conditions)
          |> (fun r -> r - no_conditions)
          |> List.nth formals in
        let args = Array.to_iter args |> Iter.map (PCFML.extract_expr ~rel) |> Iter.to_list in
        name, ty, inv, args in
      let post_param_values, expr_values, constraints =
        let (`Lambda (params, body)) = StringMap.find f_name env in
        let env = List.combine params f_args
                  |> List.map (function
                    | `Var (name, _), value -> (name, value)
                    | _ -> failwith "tuple parameters in higher order functions not supported")
                  |> StringMap.of_list in

        (** During symbolic execution and elsewhere in the system, we
           represent heap values as [PointsTo(var, _, body)], where if
           [var] is an array, then [body] will be annotated with the
           form [`App ("CFML.WPArray.Array", [_])] to capture the fact
           that var points to an array. As such, when we return the
           results of symbolic execution to Z3, we must make sure to
           strip these annotations *)
        let unwrap_heap_expression  (expr: Lang.Expr.t) =
          match expr with
          | `App ("CFML.WPArray.Array", [vl]) -> vl
          | `App (fname, _) ->
            Log.warn (fun f -> f "ignoring possible application %s@." fname);
            expr
          | _ -> expr in
        let rec eval_expr (env: (Lang.Expr.t * Lang.Type.t) StringMap.t) (sym_heap: Proof_spec.Heap.Heap.t)
                  (body: Lang.Expr.t) =
          Lang.Expr.subst Fun.(Option.map fst % flip StringMap.find_opt env) body in

        let rec eval_stmt (env: (Lang.Expr.t * Lang.Type.t) StringMap.t)
                  (sym_heap: Proof_spec.Heap.Heap.t) constraints (body: Lang.Expr.t Lang.Program.stmt) =
          match body with
          | `Write (arr, i, vl, rest) ->
            let vl = eval_expr env sym_heap vl in
            let i = eval_expr env sym_heap (`Var i) in
            let ty,arr_vl = Proof_spec.Heap.Heap.get_with_ty arr sym_heap in
            let c1 : Lang.Expr.t list =  [] (* [`App ("<", [i; `App ("TLC.LibListZ.length", [arr_vl])])] *) in
            let sym_heap =
              let arr_vl = `App ("Array.set", [arr_vl; i; vl]) in
              Proof_spec.Heap.Heap.add_heaplet
                (Proof_spec.Heap.Heaplet.PointsTo (arr, ty, `App ("CFML.WPArray.Array", [arr_vl]))) sym_heap in
            eval_stmt env sym_heap (c1 @ constraints) rest
          | `Value expr ->
            let should_unwrap = match expr with
              | `Var v ->
                Proof_spec.Heap.Heap.mem_var v sym_heap
              | _ -> false in 
            let res = eval_expr env sym_heap expr in
            let res = if should_unwrap then unwrap_heap_expression res else res in
            
            res, constraints, sym_heap
          | _ -> failwith (Format.sprintf "unsupported higher order function body %s" (Lang.Program.show_stmt
                                                                                         Lang.Expr.print_simple
                                                                                         body)) in
        let (res, constraints, sym_heap) = eval_stmt env sym_heap [] body in
        let post_expr_values =
          Proof_spec.Heap.Heap.to_list sym_heap
          |> List.map (fun (Proof_spec.Heap.Heaplet.PointsTo (var, _, expr)) ->
            StringMap.find var hole_binding,
            unwrap_heap_expression expr
          )
          |> List.map (fun (id, expr) ->
            let var_id = build_hole_var id in
            id, fun hole ->
              Lang.Expr.subst (function
                | s when String.equal var_id s -> Some hole
                | _ -> None
              ) expr
          )
          |> fun mapping ->
          match mapping with
          | [] -> [| |]
          | mapping ->
            let imap = IntMap.of_list mapping in
            let len = fst (IntMap.max_binding imap) + 1 in
            Array.init len (Fun.flip IntMap.find imap) in

        let post_param_values =
          let subst expr =
            Lang.Expr.subst (function
                | s when String.equal post_name s -> Some res
                | _ -> None
              ) expr in
          post_args
          |> List.map subst in
        let constraints = List.map (fun v -> `Assert v) constraints in
        post_param_values, post_expr_values, constraints in
      let assumptions = constraints @ List.map (fun (ty, l, r) -> `Eq (ty, l, r)) assums in
      let res : PV.vc = {
        qf=params;
        param_values=init_param_values;
        assumptions;
        post_param_values;
        expr_values;
      } in
      res
    | _ ->
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] in (%s) which was \
         expected to be a invariant spec. Expecting (SPEC (..) PRE (..) POST(..))"
        (Proof_utils.Debug.constr_to_string c)
        (Proof_utils.Debug.tag c)
        (Proof_utils.Debug.constr_to_string_pretty c) in
  collect_params [] c

(** [unwrap_instantiated_specification t env hb pre trm] when given a
   term [trm] representing the type of an instantiated specification
   extracts a triple of [formals, conditions, initial_args].

    [hole_binding] is a mapping from heap variables (i.e [arr], [r],
   etc.) to an integer id that represents the position of the
   expression that should describe the heap variable's contents in the
   result. *)
let unwrap_instantiated_specification (t: Proof_context.t) env hole_binding sym_heap (c: Constr.t) =
  (* collect invariants first accumulates the list of formal
     parameters, and then calls {!collect_invariant_conditions} to
     collect invariant conditions.Z

     Example:

     [forall (A: Type) (x: A) ..., (forall x: int, SPEC (f x) PRE _
     POST _) -> SPEC (iter _) PRE _ POST _] *)
  let rec collect_invariants acc c = 
    match Constr.kind_nocast c with
    (* we assume named arguments are formal parameters *)
    | Constr.Prod ({binder_name=Name name;_}, ty, rest) when PU.is_unnamed_prod ty ->
      collect_invariants ((Names.Id.to_string name, PCFML.unwrap_invariant_type ty) :: acc) rest
    (* as soon as we hit a named argument, we know we have stumbled
       upon the first invariant condition.  *)
    | Constr.Prod (_, ty, _) when not @@ PU.is_unnamed_prod ty ->
      collect_invariant_conditions acc [] c
    | _ -> 
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] \
         in (%s) which was expected to be \
         a specification"
        (Proof_utils.Debug.constr_to_string c) (Proof_utils.Debug.tag c) (Proof_utils.Debug.constr_to_string_pretty c) 
  (* collect invariant conditions, assumes that all the formals have
     been collected, and now the remaining arguments are higher-order
     constraints ending in a hoare Triple of the higher order iterator
     itself. *)
  and collect_invariant_conditions formals acc c =
    match Constr.kind_nocast c with
    (* if it's a prod, then this must be an pure condition  *)
    | Constr.Prod (_, ty, rest) ->
      collect_invariant_conditions formals
        ((unwrap_invariant_spec formals env hole_binding sym_heap (List.length acc) ty) :: acc) rest
    (* otherwise, we've reached the end, and our type MUST be that of
       a hoare triple: *)
    | Constr.App (triple, [| term; _; _; pre; post |]) when PU.is_const_eq "CFML.SepLifted.Triple" triple ->
      let initial_inv_args = 
        let _, args = pre |> Constr.destApp in
        Array.to_iter args |> Iter.map PCFML.extract_expr |> Iter.to_list in
      formals, acc, initial_inv_args
    | _ -> 
      Format.ksprintf ~f:failwith
        "found unhandled Coq term (%s)[%s] \
         in (%s) which was expected to be \
         a specification (expecting \
         specification invariants)"
        (Proof_utils.Debug.constr_to_string c) (Proof_utils.Debug.tag c) (Proof_utils.Debug.constr_to_string_pretty c) 
  in
  collect_invariants [] c

(** [build_verification_condition ctx defs spec] given a higher order
   specification [spec] to be applied to the current CFML goal in the
   Coq context [ctx], builds a verification condition that can be used
   to filter candidate expressions for any higher order invariants for
   the specification. *)
let build_verification_condition (t: Proof_context.t) (defs: PV.def_map) (spec: Names.Constant.t) : PV.verification_condition =
  (* extract CFML goal *)
  let (pre, post) = Proof_utils.CFML.extract_cfml_goal (Proof_context.current_goal t).ty in
  (* extract the Coq-name for the function being called, and the arguments being passed to it *)
  let (fname, args) = PCFML.extract_app_full post in
  (* instantiate specification *)
  let instantiated_spec =
    Format.ksprintf "%s %s"
      (Names.Constant.to_string spec)
      (List.map (fun (vl,ty) -> "(" ^ Proof_utils.Printer.show_expr vl ^ ": " ^ Proof_utils.Printer.show_ty ty ^ ")") args
       |> String.concat " ")
      ~f:(Proof_context.typeof t) in

  (* extract polymorphic variables and typing env *)
  let poly_vars, env = PCFML.extract_env ((Proof_context.current_goal t).hyp) in
  (* extract initial equalities in the context *)
  let assumptions = PCFML.extract_assumptions (Proof_context.current_goal t).hyp in
  (* from the pre condition, build a symbolic heap and a set of initial expressions *)
  let sym_heap, (initial_values, hole_binding) =
    let hole_count = ref 0 in
    List.filter_map
      (function `Impure heaplet -> Some (PCFML.extract_impure_heaplet heaplet) | _ -> None)
      (match pre with | `Empty -> [] | `NonEmpty ls -> ls)
    |> List.map Proof_spec.Heap.Heaplet.(function
      | PointsTo (var, ty, `App (fname, [arg])) ->
        let id = !hole_count in
        incr hole_count;
        PointsTo (var, ty, `App (fname, [`Var (build_hole_var id)])), (arg, (var, id))
      | _ -> failwith "unsupported heaplet"
    )
    |> List.split
    |> Pair.map_snd (List.split) in
  let hole_binding = StringMap.of_list hole_binding in
  let initial_values = Array.of_list initial_values in
  let sym_heap = Proof_spec.Heap.Heap.of_list sym_heap in
  let invariants, conditions, args = unwrap_instantiated_specification t defs hole_binding sym_heap instantiated_spec in
  (* only 1 invariant supported for now *)
  assert (List.length invariants = 1);

  let functions =
    List.fold_left (fun funs (_,l, r) ->
      Lang.Expr.functions (Lang.Expr.functions funs l) r) StringSet.empty assumptions
    |> Fun.flip (Array.fold Lang.Expr.functions) initial_values
    |> Fun.flip (List.fold_left Lang.Expr.functions) args
    |> Fun.flip (List.fold_left (fun funs (condition: PV.vc) ->
      List.fold_left Lang.Expr.functions funs condition.param_values
      |> Fun.flip (List.fold_left Lang.Expr.functions) condition.post_param_values
      |> Fun.flip (List.fold_left
                     (fun funs -> function
                        | `Eq (_, l, r) ->
                          Lang.Expr.functions (Lang.Expr.functions funs l) r
                        |`Assert bool ->
                          Lang.Expr.functions funs bool))
           condition.assumptions
      |> Fun.flip (Array.fold (fun funs hexpr -> Lang.Expr.functions funs (hexpr (`Var "??"))))
            condition.expr_values
    )) conditions
    |> StringSet.to_list in
  let functions = List.filter_map (function
      ("-" | "+" | "*" | "Array.set" | "CFML.WPArray.Array") -> None
    | fn -> Some fn
  ) functions in

  let properties =
    let eq_query = 
      let eq = Libnames.qualid_of_string "Coq.Init.Logic.eq" |> Nametab.locate in
      true, Search.(GlobSearchLiteral
                      (GlobSearchSubPattern (
                         Vernacexpr.InConcl, false, Pattern.PRef eq
                       ))) in
    let cmp_query cmp = 
      let eq = Libnames.qualid_of_string ("TLC.LibOrder." ^ cmp) |> Nametab.locate in
      false, Search.(GlobSearchLiteral
                      (GlobSearchSubPattern (
                         Vernacexpr.Anywhere, false, Pattern.PRef eq
                       ))) in
    let prop_query =
      true, Search.GlobSearchDisjConj [
        [eq_query];
        [cmp_query "lt"];
        [cmp_query "gt"];        
        [cmp_query "ge"];
        [cmp_query "gt"];
      ] in
    let query v =
      let fn = Libnames.qualid_of_string v |> Nametab.locate_constant in
      true, Search.(GlobSearchLiteral
                      (GlobSearchSubPattern (
                         Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef fn)
                       ))) in
    Fun.flip List.flat_map functions @@ fun name ->
    Proof_context.search t [
      prop_query;
      query name;
    ]
    |> List.filter_map (fun (name, _, constr) ->
      match extract_property constr with
      | Ok prop -> Some (name, prop)
      | Error e ->
        Log.warn (fun f -> f "failed to extract %s (%s) @.@." (globref_to_string name) e);
        None
    )
    |> List.filter (function
        (name, (_, _, _, `Eq (Lang.Type.Var "HPROP", _, _))) -> false
      | _ -> true)
  in

  let functions =
    List.fold_left (fun s (_, p) -> PV.property_functions s p) (StringSet.of_list functions) properties
    |> StringSet.to_list in


  Log.debug (fun f -> f "functions: %s@." (List.to_string Fun.id (functions)));


  let functions = List.filter_map (function
      ("-" | "+" | "*" | "Array.set" | "CFML.WPArray.Array" | "TLC.LibContainer.update"
      | "TLC.LibOrder.ge" | "TLC.LibOrder.gt" | "TLC.LibOrder.lt" | "TLC.LibOrder.le") -> None
    | fn ->
      let typ = Proof_context.typeof t fn in
      let name = Libnames.qualid_of_string fn |> Nametab.locate_constant in
      try
        let typ = Proof_utils.CFML.extract_fun_typ ~name typ in
        Some (fn, typ)
      with _ -> None
  ) functions in

  let supported_functions =
    List.map (fun (name, _) -> name) functions
    |> StringSet.of_list
    |> StringSet.union (StringSet.of_list [
      "-" ; "+" ; "*" ;
      "Array.set" ;
      "CFML.WPArray.Array";
      "TLC.LibContainer.update";
      "TLC.LibOrder.ge";
      "TLC.LibOrder.gt";
      "TLC.LibOrder.lt";
      "TLC.LibOrder.le"
    ]) in

  let properties = 
    properties
    |> List.filter (fun (_, prop) -> PV.property_only_uses_functions_in supported_functions prop)
    |> List.map (Pair.map_fst globref_to_string) in


  {
    poly_vars;
    functions;
    properties;
    invariant=List.hd invariants;
    env;
    assumptions;
    initial={
      expr_values=initial_values;
      param_values=args;
    };
    conditions;
  }
