open Containers

let drop_last ls =
  let rec loop acc = function
    | [] | [_] -> List.rev acc
    | h :: t -> loop (h :: acc) t in
  loop [] ls


module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type coq_ctx = (module Coq.Proof.PROOF)

type t = {
  ctx: coq_ctx;
  mutable current_program_id: Lang.Id.t;
  alignment: Dynamic.Matcher.t;
}

let next_program_id t =
  t.current_program_id <- Lang.Id.incr t.current_program_id

let append {ctx; _} =
  let module Ctx = (val ctx) in
  Format.ksprintf ~f:(fun res ->
    Ctx.add res;
    Ctx.exec ()
  )

let extract_proof_script {ctx; _} =
  let module Ctx = (val ctx) in
  let proof_length = Ctx.size () in
  let buf = Buffer.create 100 in
  for at = proof_length - 1 downto 0 do
    let ast =
      match Ctx.query ~at Serapi.Serapi_protocol.Ast with
      | Some [Serapi.Serapi_protocol.CoqAst ast] -> ast
      | _ -> failwith "unexpected response from Serapi" in
    let ast_str =
      Proof_debug.coqobj_to_string (Serapi.Serapi_protocol.CoqAst ast) in
    Buffer.add_string buf ast_str;
    Buffer.add_string buf "\n";
  done;
  Buffer.contents buf

let subproofs {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some goals -> goals
  | None -> failwith "unable to retrieve subproofs - serapi returned None."

let current_subproof {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Goals
  |> Option.map @@ List.map (function[@warning "-8"]
    | Serapi.Serapi_protocol.CoqGoal g -> g
  )
  |> function
  | Some (goal :: _) -> goal
  | Some [] -> failwith "failed to obtain subproof - serapi returned no remaining subproofs."
  | None -> failwith "unable to retrieve subproof - serapi returned None."

let current_goal t =
  match (current_subproof t).goals with
  | [goal] -> goal
  | [] -> failwith "failed to obtain focused goal - serapi returned no focused goals."
  | _ -> failwith "failed to obtain focused goal - serapi returned multiple focused goals"

let env {ctx; _} =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.Env
  |> Option.flat_map (fun env ->
    match env with
    |[Serapi.Serapi_protocol.CoqEnv env] -> Some env
    | _ -> None
  )
  |> function
  | Some v -> v
  | None -> failwith "unable to obtain proof env - serapi returned None."

let search t query =
  let env = env t in
  let evd = Evd.from_env env in
  let acc = ref [] in
  Search.search env evd query ([], false) (fun refr kind _ typ ->
    acc := (refr,kind,typ) :: !acc
  );
  !acc

let find_spec t const =
  search t [
    true, Search.(GlobSearchLiteral (GlobSearchString "spec"));
    true, Search.(GlobSearchLiteral
                    (GlobSearchSubPattern (Vernacexpr.InConcl, false, Pattern.PRef (Names.GlobRef.ConstRef const))))
  ] |> function
  | [(Names.GlobRef.ConstRef name, _, ty)] -> (name, ty)
  | [_] -> failwith "failure finding specification for function application: non-constant name for reference"
  | [] -> failwith "failure finding specification for function application: could not find an appropriate specification"
  | _ -> failwith "failure finding specification for function application: ambiguity - more than one valid specification found"

let pretty_print_current_goal t =
  let env = env t in
  print_endline @@ "current goal: \n" ^
                   Format.sprintf "%a" Pp.pp_with
                     (Serapi.Serapi_protocol.gen_pp_obj
                        env Evd.empty (Serapi.Serapi_protocol.CoqGoal (current_subproof t)))
let debug_print_current_goal t =
  print_endline @@ "current goal: \n" ^ Proof_debug.constr_to_string (current_goal t).ty

let current_names t =
  let goal = current_goal t in
  goal.hyp
  |> List.to_iter
  |> Iter.filter_map (fun (name, _, _) -> List.last_opt name)
  |> Iter.map Names.Id.to_string
  |> StringSet.of_iter

let fresh ?(base="tmp") t =
  let names = current_names t in
  let name_in_use name =
    StringSet.mem name names in
  let rec loop incr =
    let name = Format.sprintf "%s%d" base incr in 
    if name_in_use name
    then loop (incr + 1)
    else name in
  if name_in_use base
  then loop 0
  else base

let init ~prelude ~spec ~alignment ~ctx =
  let module Ctx = (val ctx : Coq.Proof.PROOF) in
  Ctx.reset ();
  Ctx.add prelude;
  Ctx.add spec;
  Ctx.exec ();
  {
    ctx;
    alignment;
    current_program_id=Lang.Id.init
  }

type constr = Constr.constr
let pp_constr fmt v =
  Format.pp_print_string fmt @@ Proof_debug.constr_to_string v

let show_preheap = [%show: [> `Empty | `NonEmpty of [> `Impure of constr | `Pure of constr ] list ]]

let rec symexec t env (body: Lang.Expr.t Lang.Program.stmt) =
  match body with
  | `LetLambda (name, body, rest) ->
    symexec_lambda t env name body rest
  | `LetExp (pat, rewrite_hint, body, rest) ->
    begin match body with
    | `App ("Array.make", [_; _]) ->
      symexec_alloc t env pat rest
    | `App (_, prog_args)
      when List.exists (function
        |`Var v -> StringMap.find_opt v env |> Option.exists Program_utils.is_pure
        | _ -> false
      ) prog_args ->
      symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest      
    | `App (_, args)
      when List.exists (function
        |`Var v -> StringMap.mem v env
        | _ -> false
      ) args ->
      symexec_higher_order_fun t env pat rewrite_hint args body rest
    | _ -> symexec_opaque_let t env pat rewrite_hint body rest
    end
  | `Match (prog_expr, cases) ->
    symexec_match t env prog_expr cases
  | `EmptyArray ->
    append t "xvalemptyarr."
  | `Write _ -> failwith "don't know how to handle write"
  | `Value _ -> failwith "don't know how to handle value"
and symexec_lambda t env name body rest =
  let fname = fresh ~base:name t in
  let h_fname = fresh ~base:("H" ^ name) t in
  append t "xletopaque %s %s." fname h_fname;
  let env = StringMap.add name body env in
  symexec t env rest
and symexec_alloc t env pat rest =
  let prog_arr = match pat with
    | `Tuple _ -> failwith "found tuple pattern in result of array.make"
    | `Var (var, _) -> var in
  let arr = fresh ~base:(prog_arr) t in
  let data = fresh ~base:"data"  t in
  let h_data = fresh ~base:("H" ^ data) t in
  append t "xalloc %s %s %s." arr data h_data;
  symexec t env rest
and symexec_opaque_let t env pat _rewrite_hint body rest =
  let prog_var = match pat with
    | `Tuple _ ->
      failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")
    | `Var (var, _) -> var in
  let var = fresh ~base:(prog_var) t in
  let h_var = fresh ~base:("H" ^ var) t in
  append t "xletopaque %s %s."  var h_var;
  symexec t env rest
and symexec_match t env prog_expr cases =
  (* emit a case analysis to correspond to the program match    *)
  (* for each subproof, first intro variables using the same names as in the program *)
  let case_intro_strs =
    List.map (fun (_, args, _) ->
      List.map (fun (name, _) ->
        fresh ~base:(name) t
      ) args
      |> String.concat " "
    ) cases in
  (* preserve the equality of the program expression *)
  let eqn_var = fresh ~base:("H_eqn") t in
  (* emit a case analysis: *)
  append t "case %a as [%s] eqn:%s."
    Printer.pp_expr prog_expr
    (String.concat " | " case_intro_strs)
    eqn_var;

  (* now, handle all of the sub proofs *)
  List.iter (fun (_, _, rest) ->
    (* start each subproof with an xmatch to determine the appropriate branch *)
    append t "- xmatch.";
    (* now emit the rest *)
    symexec t env rest;
    (* dispatch remaining subgoals by the best method: *)
    while (current_subproof t).goals |> List.length > 0 do 
      append t "{ admit. }";
    done;
  ) cases
and symexec_higher_order_pure_fun t env pat rewrite_hint prog_args rest =
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let (_, post) = Proof_cfml.extract_cfml_goal (current_goal t).ty in
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
      let ty = fresh ~base:("ty_" ^ name ) t in
      append t "evar (%s: Type)." ty;
      let name = fresh ~base:name t in
      append t "evar (%s: %s)." name ty;
      to_clear
      |> List.cons ty
      |> List.cons name
    ) [] evar_params |> List.rev in

  (* emit xapp call *)
  let fn_body =
    List.find_map (function
        `Var v -> StringMap.find_opt v env |> Option.flat_map (Option.if_ Program_utils.is_pure)
      | _ -> None) prog_args
    |> Option.get_exn_or "invalid assumptions" in

  append t "xapp (%s %s %s %s)."
    (Names.Constant.to_string f_name)
    (List.map (Printer.show_expr) prog_args |> String.concat " ")
    (List.map (fun (name, _) -> "?" ^ Format.to_string Pp.pp_with (Names.Name.print name))
       evar_params
     |> String.concat " ")
    (Printer.show_lambda fn_body);

  (* solve immediate subgoal of xapp automatically. *)
  append t "sep_solve.";

  (* TODO: repeat based on goal shape, not no goals   *)
  (* any remaining subgoals we assume we can dispatch automatically by eauto. *)
  while List.length (current_subproof t).goals > 1 do
    append t "eauto.";
  done;

  (* finally, clear any evars we introduced at the start  *)
  append t "clear %s." (String.concat " " clear_vars);

  (* destructuring of arguments *)
  begin
    match pat with
    | `Var _ -> ()
    | `Tuple vars ->
      (* if we have a tuple, then we need to do some extra work *)
      let vars = List.map (fun (name, _) ->
        fresh ~base:name t
      ) vars in
      let h_var = fresh ~base:("H" ^ String.concat "" vars) t in
      (* first, emit a xdestruct to split the tuple output - [hvar] remembers the equality *)
      append t "xdestruct %s %s." (String.concat " " vars) h_var;
      (* next, use a user-provided rewrite hint to simplify the equality  *)
      begin match rewrite_hint with
      | Some rewrite_hint ->
        append t "rewrite %s in %s." rewrite_hint h_var;
      | None ->
        failwith "tuple destructuring with functions requires a rewrite hint."
      end;
      (* finally, split the simplified equality on tuples into an equality on terms  *)
      let split_vars = List.map (fun var -> fresh ~base:("H" ^ var) t) vars in
      append t "injection %s; intros %s."
                            h_var (String.concat " " @@ List.rev split_vars);
  end;
  symexec t env rest
and symexec_higher_order_fun t env pat rewrite_hint prog_args body rest =
  pretty_print_current_goal t;
  debug_print_current_goal t;
  let (pre, post) = Proof_cfml.extract_cfml_goal (current_goal t).ty in
  print_endline @@ show_preheap pre;
  (* work out the name of function being called and the spec for it *)
  let (f_name, raw_spec) =
    (* extract the proof script name for the function being called *)
    let f_app = Proof_cfml.extract_x_app_fun post in
    (* use Coq's searching functionality to work out the spec for the function *)
    find_spec t f_app in

  print_endline @@ Printf.sprintf "lemma is %s, spec is %s"
                     (Names.Constant.to_string f_name)
                     (Proof_debug.constr_to_string raw_spec);
  let (params, invariant, spec) = Proof_cfml.extract_spec raw_spec in

  let name_to_string name = Format.to_string Pp.pp_with (Names.Name.print name) in

  print_endline @@
  Printf.sprintf "params are: %s" 
    (List.map (fun (name, _) -> name_to_string name) params |> String.concat ", ");

  print_endline @@
  Printf.sprintf "invariants are: %s" 
    (List.map (fun (_, sg) -> Proof_debug.constr_to_string sg) invariant |> String.concat ", ");

  failwith ("TODO: implement handling of let _ = " ^ Format.to_string Lang.Expr.pp body ^ " expressions")

let generate t (prog: Lang.Expr.t Lang.Program.t) =
  append t {|xcf.|};
  let pre, _ = Proof_cfml.extract_cfml_goal (current_goal t).ty in

  (* handle pure preconditions *)
  begin match pre with
  | `NonEmpty ls ->
    let no_pure = List.count (function `Pure _ -> true | _ -> false) ls in
    let pat = 
      Int.range 1 no_pure
      |> Iter.map (fun i -> "H" ^ Int.to_string i)
      |> Iter.concat_str in
    append t "xpullpure %s." pat;
  | _ -> ()
  end;
  symexec t StringMap.empty prog.body;
  extract_proof_script t

