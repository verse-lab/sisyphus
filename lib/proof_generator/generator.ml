open Containers

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

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let arg_list_to_str args =
  (List.map (fun vl -> "(" ^ Proof_utils.Printer.show_expr vl ^ ")") args
   |> String.concat " ")

let find_spec t const =
  Proof_context.search t [
    true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
    true, Search.(GlobSearchLiteral
                    (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef const))))
  ] |> function
  | [(Names.GlobRef.ConstRef name, _, ty)] -> (name, ty)
  | [_] -> failwith "failure finding specification for function application: non-constant name for reference"
  | [] -> failwith "failure finding specification for function application: could not find an appropriate specification"
  | _ -> failwith "failure finding specification for function application: ambiguity - more than one valid specification found"

type constr = Constr.constr
let pp_constr fmt v =
  Format.pp_print_string fmt @@ Proof_utils.Debug.constr_to_string v

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
let build_complete_params t lemma_name init_params =
  let mk_lemma_instantiated_type params = 
    Format.ksprintf ~f:(Proof_context.typeof t)
      "%s %s"
      (Names.Constant.to_string lemma_name)
      (arg_list_to_str params) in
  let rec loop params lemma_instantiated_type =
    match Constr.kind lemma_instantiated_type with
    | Prod (Context.{binder_name; _}, ty, _) ->
      let evar_name = Proof_context.fresh
                        ~base:(Format.to_string Pp.pp_with @@ Names.Name.print binder_name)
                        t in
      Proof_context.append t "evar (%s: %s)." evar_name
        (Proof_utils.Debug.constr_to_string_pretty ty);
      let params = params @ [`Var evar_name] in
      let lemma_instantiated_type = mk_lemma_instantiated_type params in
      loop params lemma_instantiated_type
    | _ -> params, lemma_instantiated_type in
  loop init_params (mk_lemma_instantiated_type init_params)

(** [instantiate_arguments t env args (ctx, heap_ctx)] attempts to
   instantiate a list of concrete arguments [args] using an observed
   context [ctx] and heap state [heap_ctx] from an execution trace.
   To do this, it may introduce additional evars in proof context [t]
   to represent polymorphic values. *)
let instantiate_arguments t env args (ctx, heap_ctx) =
    let open Option in
    List.map (fun (vl, ty) ->
      match vl with
        `Var v ->
        begin match StringMap.find_opt v env.Proof_env.bindings with
        | None -> Some (`Var v)
        | Some v ->
          Option.or_lazy
            (List.Assoc.get ~eq:String.equal v ctx |> Option.flat_map (Proof_context.eval_tracing_value t ty))
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
        end                
      | expr -> Some expr
    ) args
    |> List.all_some

let rec symexec (t: Proof_context.t) env (body: Lang.Expr.t Lang.Program.stmt) =
  (* Format.printf "current program id is %s: %s@."
   *   (t.Proof_context.current_program_id |>  Lang.Id.show)
   *   (Lang.Program.show_stmt_line Lang.Expr.print body |> String.replace ~sub:"\n" ~by:" "); *)
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
      ) prog_args ->
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
  | `Value _ -> failwith "don't know how to handle value"
and symexec_lambda t env name body rest =
  let fname = Proof_context.fresh ~base:name t in
  let h_fname = Proof_context.fresh ~base:("H" ^ name) t in
  Proof_context.append t "xletopaque %s %s." fname h_fname;
  let env = Proof_env.add_lambda_def t env name body in
  update_program_id_over_lambda t body;
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
    let (_, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in
  let (params, invariant, spec) = Proof_cfml.extract_spec raw_spec in

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
  let (pre, post) = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in
  (* work out the name of function being called and the spec for it *)
  let (lemma_name, lemma_full_type) =
    (* extract the proof script name for the function being called *)
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in

  let (lemma_params, lemma_invariants, spec) = Proof_cfml.extract_spec lemma_full_type in
  let explicit_lemma_params = Proof_utils.drop_implicits lemma_name lemma_params in
  let (_, _f_args) = Proof_cfml.extract_app_full t post in


  let param_bindings, remaining = combine_rem explicit_lemma_params _f_args in
  match remaining with
  | Some (Right _) | None | Some (Left [])  ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with no invariant/insufficient arguments?"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left (_ :: _ :: _)) ->
    Format.ksprintf ~f:failwith "TODO: found function application %a with multiple invariants"
      Pp.pp_with (Names.Constant.print lemma_name)
  | Some (Left [(inv, inv_ty)]) ->

    let _vc =
      Specification.build_verification_condition t
        (Proof_env.env_to_defmap env) lemma_name in

    let cp = t.Proof_context.concrete () in
    let observations =
      Dynamic.Concrete.lookup cp
        (t.Proof_context.current_program_id :> int) in

    let show_obs obs =
      [%show: (string * Dynamic.Concrete.value) list *
              (string * Dynamic.Concrete.heaplet) list] obs in
    let _ =
      List.find_map Option.(fun obs ->
        print_endline @@ show_obs obs;
        print_endline "with temporary context START";
        let v = Proof_context.with_temporary_context t begin fun () ->
          (* first, instantiate the concrete arguments using values from the trace *)
          let* instantiated_params = instantiate_arguments t env _f_args obs in
          (* next, add evars for the remaining arguments to lemma *)
          let lemma_complete_params, _ =
            build_complete_params t lemma_name instantiated_params in
          (* construct term to represent full application of lemma parameters *)
          let trm = 
            Format.ksprintf ~f:(Proof_context.term_of t) "%s %s"
              (Names.Constant.to_string lemma_name)
              (arg_list_to_str  lemma_complete_params) in

          let env = Proof_context.env t in
          let evd = Evd.from_env env in
          let (evd, reduced) =
            Proof_reduction.reduce
              ~filter:(fun ~path ~label ->
                (* Format.printf "checking %s . %s ==> YES@." path label; *)
                `Unfold)
              env evd (Evd.MiniEConstr.of_constr trm) in

          let reduced = EConstr.to_constr evd reduced in
          print_endline "DONE";
          (* Format.printf "instantiated lemma is %s@."
           *   (Proof_utils.Debug.constr_to_string_pretty reduced); *)
          let _ = Proof_analysis.analyse reduced in


          Some trm
        end in
        print_endline "with temporary context END";
        v
      ) observations
    in


    let _ = 
      List.map (fun (_param, (supplied_expr, supplied_ty)) ->
        supplied_expr
      ) param_bindings in



    (* =====================printing starts========================================= *)
    Format.printf "inv is %a@." Pp.pp_with (Names.Name.print inv);
    let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name) in
    print_endline @@
    Printf.sprintf "params are: %s"
      (List.map (fun (name, _) -> name_to_string name) lemma_params |> String.concat ", ");

    print_endline @@
    Printf.sprintf "invariants are: %s" 
      (List.map (fun (_, sg) -> Proof_utils.Debug.constr_to_string sg) lemma_invariants |> String.concat ", ");

    print_endline @@
    Printf.sprintf "real params are: %s" 
      (List.map (fun (name, _) -> name_to_string name) explicit_lemma_params |> String.concat ", ");

    print_endline @@ Format.sprintf "args: (%s)"@@
    (List.map (fun (exp, _) -> Lang.Expr.show exp) _f_args |> String.concat ", ");

    failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")

let generate t (prog: Lang.Expr.t Lang.Program.t) =
  Proof_context.append t {|xcf.|};
  let pre, _ = Proof_cfml.extract_cfml_goal (Proof_context.current_goal t).ty in

  (* handle pure preconditions *)
  begin match pre with
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    let pat = 
      Int.range 1 no_pure
      |> Iter.map (fun i -> "H" ^ Int.to_string i)
      |> Iter.concat_str in
    Proof_context.append t "xpullpure %s." pat;
  | _ -> ()
  end;
  symexec t Proof_env.initial_env prog.body;
  Proof_context.extract_proof_script t

