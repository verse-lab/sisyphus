open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type coq_ctx = (module Coq.Proof.PROOF)

type t = {
  mutable generated_proof_script: string list;
  compilation_context: Dynamic.CompilationContext.t;
  old_proof: Proof_spec.Script.script;
  ctx: coq_ctx;
  mutable current_program_id: Lang.Id.t;
  alignment: Dynamic.Matcher.t;
  concrete: unit -> Dynamic.Concrete.t;
}

(** [cancel_last t] reverts the proof context [t] to the state it was
   before the most recently executed command.  *)
let cancel_last ({ctx;_} as prf) =
  let module Ctx = (val ctx) in
  prf.generated_proof_script <- List.tl prf.generated_proof_script;
  Ctx.cancel_last ()

(** [cancel t ~count] reverts the proof context [t] to the state it
   was before the [count] most recently executed commands.  *)
let cancel ({ctx;_} as prf) ~count =
  let module Ctx = (val ctx) in
  prf.generated_proof_script <- List.drop count prf.generated_proof_script;
  Ctx.cancel ~count

(** [next_program_id t] updates the proof context to record that the
   program state has moved to the next program id. *)
let next_program_id t =
  t.current_program_id <- Lang.Id.incr t.current_program_id

(** [append t fmt ...] updates the proof context with the result of
   executing the command returned by [sprintf fmt ...].  *)
let append ({ctx; _} as prf) =
  let module Ctx = (val ctx) in
  Format.ksprintf ~f:(fun res ->
    prf.generated_proof_script <- res :: prf.generated_proof_script;
    Ctx.add res;
    Ctx.exec ()
  )

(** [extract_proof_script t] returns the current proof script state
   from the proof context [t]. *)
let extract_proof_script ({ctx; _} as t) =
  let module Ctx = (val ctx) in
  (List.rev t.generated_proof_script |> String.concat "\n")

(** [subproofs t] returns all the subproofs of the current goal, raising an exception if there are no subproofs. *)
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

let typeof t expr =
  let no_hyps = List.length (current_goal t).hyp in
  append t "pose proof (%s)." expr;
  if List.length (current_goal t).hyp <= no_hyps then
    Format.ksprintf
      ~f:failwith "attempted to check type of invalid expression (%s)." expr;
  let (_, _, ty) = List.hd (current_goal t).hyp in
  let module Ctx = (val t.ctx) in
  cancel_last t;
  ty

let term_of t expr =
  let no_hyps = List.length (current_goal t).hyp in
  append t "pose (%s)." expr;
  if List.length (current_goal t).hyp <= no_hyps then
    Format.ksprintf
      ~f:failwith "attempted to check type of invalid expression (%s)." expr;
  let (_, def, _) = List.hd (current_goal t).hyp in
  let module Ctx = (val t.ctx) in
  cancel_last t;
  Option.get_exn_or "invalid assumptions" def

let definition_of {ctx; _} txt =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.(TypeOf txt)
  |> Option.flat_map Serapi.Serapi_protocol.(function
    |[CoqMInd (name, def)] -> Some def
    | _ -> None    
  )

let names {ctx; _} txt =
  let module Ctx = (val ctx) in
  Ctx.query Serapi.Serapi_protocol.(Names txt)
  |> Option.flat_map Serapi.Serapi_protocol.(function
    | CoqGlobRef name :: _ -> Some name
    | _ -> None    
  )
  
let constant t txt =
  names t txt |> Option.map begin function
  | Names.GlobRef.ConstRef c -> c

  | Names.GlobRef.VarRef _ ->
    failwith (Format.sprintf "name %s resolved to var when expecting a const." txt)
  | Names.GlobRef.IndRef _ ->
    failwith (Format.sprintf "name %s resolved to ind when expecting a const." txt)
  | Names.GlobRef.ConstructRef _ ->
    failwith (Format.sprintf "name %s resolved to a constructor when expecting a const." txt)
  end

let search t query =
  let env = env t in
  let evd = Evd.from_env env in
  let acc = ref [] in
  Search.search env evd query ([], false) (fun refr kind _ typ ->
    acc := (refr,kind,typ) :: !acc
  );
  !acc

let pretty_print_current_goal t =
  let env = env t in
  print_endline @@ "current goal: \n" ^
                   Format.sprintf "%a" Pp.pp_with
                     (Serapi.Serapi_protocol.gen_pp_obj
                        env Evd.empty (Serapi.Serapi_protocol.CoqGoal (current_subproof t)))

let debug_print_current_goal t =
  print_endline @@ "current goal: \n" ^ Proof_utils.Debug.constr_to_string (current_goal t).ty

let current_names t =
  let goal = current_goal t in
  goal.hyp
  |> List.to_iter
  |> Iter.filter_map (fun (name, _, _) -> List.last_opt name)
  |> Iter.map Names.Id.to_string
  |> StringSet.of_iter

(** [fresh ?base t] returns a fresh variable name that is guaranteed
   not to clash with any of the names in the proof context [t], and if
   provided has prefix [base].  *)
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

(** [with_temporary_context t f] runs the function [f] with a
   temporary proof context bound to [t].

    All bindings prior to calling the function will be present in this
   temporary context, but any new bindings will be cleared at the end
   of [f]. *)
let with_temporary_context ({ctx; _} as t) f =
  let module Ctx = (val ctx) in
  let original_proof_size = Ctx.size () in
  Fun.protect
    ~finally:(fun () ->
      let new_proof_size = Ctx.size () in
      let count = new_proof_size - original_proof_size in
      if count > 0 then
        cancel t ~count
    ) f

(** [eval_tracing_value t ty vl] given a concrete observation value
   [vl] with type [ty] will return an expression that can be sent to
   Coq.

    Note: updates the proof context with evars for any symbolic
   variables that occur in the expression.  *)
let rec eval_tracing_value t (ty: Lang.Type.t) (vl: Dynamic.Concrete.value) : Lang.Expr.t option =
  let open Option in
  match ty, vl with
  | (Lang.Type.Product tys, `Tuple vls) ->
    let+ elts = List.map2 (eval_tracing_value t) tys vls
               |> List.all_some in
    `Tuple elts
  | (Lang.Type.List ty, `List elts) ->
    eval_tracing_list t ty elts
  | (_, `Int n) -> Some (`Int n)
  | (ty, `Value vl) ->
    let var = fresh ~base:vl t in
    append t "evar (%s: %s)." var (Proof_utils.Printer.show_ty ty);
    Some (`Var var)
  | (_ , `Constructor _) -> None (* todo: implement handling of constructors *)
  | _ -> None

(** [eval_tracing_list t ty elts] given a list of concrete observation
   values [ls] with type [ty] will return an expression that can be
   sent to Coq.

    Note: updates the proof context with evars for any symbolic variables that occur in the expression. *)
and eval_tracing_list t ty elts =
  let open Option in
  let rec loop = function
    | [] -> Some (`Constructor ("[]", []))
    | h :: tl ->
      let* h = eval_tracing_value t ty h in
      let* tl = eval_tracing_list t ty tl in
      Some (`Constructor ("::", [h; tl])) in
  loop elts
          
let init ~compilation_context ~old_proof ~new_proof_base ~alignment ~concrete ~ctx =
  let module Ctx = (val ctx : Coq.Proof.PROOF) in
  Ctx.reset ();
  Ctx.add new_proof_base;
  Ctx.exec ();
  {
    generated_proof_script=[];
    ctx; compilation_context;
    alignment; concrete; old_proof;
    current_program_id=Lang.Id.init
  }
