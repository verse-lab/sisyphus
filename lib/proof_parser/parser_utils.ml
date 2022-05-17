open Containers
open Proof_spec.Script
module StringMap = Map.Make(String)

let unwrap_list = function
    Sexplib.Sexp.List xs -> xs
  | _ -> assert false

let unwrap_atom = function
    Sexplib.Sexp.Atom str -> str
  | _ -> assert false

let unwrap_tagged =
  let open Sexplib.Sexp in
  function [@warning "-8"]
  | List (Atom t :: args) -> t, args

let unwrap_value_binding =
  let open Sexplib.Sexp in
  function [@warning "-8"]
  | List [Atom t; arg] -> t, arg

(* [ [v ...] [loc ...]]   *)
let unwrap_binding sexp =
  sexp
  |> unwrap_list
  |> List.map unwrap_value_binding
  |> StringMap.of_list

let unwrap_value_with_loc sexp =
  let binding = unwrap_binding sexp in
  let v = StringMap.find "v" binding in
  let loc = StringMap.find "loc" binding in
  v, loc

let unwrap_genarg sexp =
  match [@warning "-8"] unwrap_tagged sexp with
  | ("GenArg", [_raw; List [Atom _; Atom _tag]; binding]) ->
    let v, loc = unwrap_value_with_loc binding in
    _tag, v

let unwrap_tacgeneric_arg sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacGeneric", [_; arg] ->
    let  [@warning "-8"] ("constr", exp) = unwrap_genarg arg in
    exp

let unwrap_cref sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "CRef", [binding; _] ->
    let v, _ = unwrap_value_with_loc binding in
    let _, [_; List [Atom "Id"; Atom cref]] = unwrap_tagged v in
    cref

let or_exn name sexp f =
  try f () with
  | Match_failure (pos,st,ed) ->
    failwith @@ Format.sprintf "unexpected form for %s (at %s:%d:%d): %a"
      name pos st ed Sexplib.Sexp.pp_hum sexp

let rec unwrap_ty sexp : Lang.Type.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ ->
    begin match unwrap_cref sexp with
      | "func" -> Func
      | "int" -> Int
      | "loc" -> Loc
      | "unit" -> Unit
      | var -> Var var
    end
  | "CApp", [fname; args] ->
    let fname =
      let fname, _ = unwrap_value_with_loc fname in
      unwrap_cref fname in
    let args = 
      let args = unwrap_list args
                 |> List.map (function List [data; _] ->
                     unwrap_value_with_loc data
                     |> fst
                     |> unwrap_ty
                   ) in
      args in
    begin match fname, args with
      | "list", [ty] -> List ty
      | "array", [ty] -> Array ty
      | "ref", [ty] -> Ref ty
      | adt, args -> ADT (adt, args, None)
    end
  | "CNotation", _ ->
    failwith @@ Format.sprintf "todo: implement support for product sexps: %a" Sexplib.Sexp.pp_hum sexp
[@@warning "-8"]


let unwrap_ty sexp =
  let open Sexplib.Sexp in
  or_exn "lambda type" sexp @@ fun () -> unwrap_ty sexp

let unwrap_lambda_arg sexp =
  let open Sexplib.Sexp in
  or_exn "lambda arg" sexp @@ fun () ->
  match unwrap_tagged sexp with
  | "CLocalAssum", [name; _; ty] ->
    let "Name", [List [Atom "Id"; Atom name]] =
      let [name] = unwrap_list name in
      unwrap_value_with_loc name
      |> fst
      |> unwrap_tagged in
    let ty =
      let ty, _ = unwrap_value_with_loc ty in
      unwrap_ty ty in
    (`Var name, ty)
[@@warning "-8"]


let unwrap_clambda sexp =
  match unwrap_tagged sexp with
  | "CLambdaN", [args; body] ->
    let args = unwrap_list args
               |> List.map unwrap_lambda_arg in

    let body, _ = unwrap_value_with_loc body in
    args, body
  | _ ->
    failwith @@ Format.sprintf "found invalid structure for clambda expression: %a" Sexplib.Sexp.pp_hum sexp

let unwrap_int_literal sexp : int =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "Number", [List [Atom "SPlus"; List [List [Atom "int"; Atom n]; _frac; _exp]]] -> int_of_string n
  | _ ->
    failwith @@ Format.sprintf "found invalid structure for literal: %a" Sexplib.Sexp.pp_hum sexp

let rec unwrap_expr sexp : Lang.Expr.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Var (unwrap_cref sexp)
  | "CPrim", [num] -> `Int (unwrap_int_literal num)
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom "( _ , _ , .. , _ )"]; List (List [fst'] :: List [List rest] :: _)] ->
    let elts = fst' :: rest in
    let elts = List.map (fun v -> unwrap_value_with_loc v |> fst |> unwrap_expr) elts in
    `Tuple elts
  | "CApp", [fname; args] ->
    let fname = fname |> unwrap_value_with_loc |> fst |> unwrap_cref in
    let args = unwrap_list args
               |> List.map (function
                     List [data; _] ->
                     unwrap_value_with_loc data
                     |> fst
                     |> unwrap_expr
                   | sexp -> failwith @@ Format.sprintf "found unexpected lambda structure in CApp %a"
                       Sexplib.Sexp.pp_hum sexp
                 ) in
    let is_uppercase c = Char.equal c (Char.uppercase_ascii c) in
    begin if String.get fname 0 |> is_uppercase
      then `Constructor (fname, args)
      else `App (fname, args)
    end
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom ("_ ++ _" | "_ + _" | "_ - _" as op)]; List (List [l; r] :: _)] ->
    let l = unwrap_value_with_loc l |> fst |> unwrap_expr in
    let r = unwrap_value_with_loc r |> fst |> unwrap_expr in
    begin match op with
      | "_ ++ _" -> `App ("++", [l;r])
      | "_ + _" -> `App ("+", [l;r])
      | "_ - _" -> `App ("-", [l;r])
      | _ -> failwith "invalid assumptions"
    end
  (* lambdas.... CLambdaN not supported *)
  | tag, _ -> failwith @@ Format.sprintf "found unhandled expr (tag: %s): %a" tag Sexplib.Sexp.pp_hum sexp

let unwrap_assertion sexp : Proof_spec.Heap.Assertion.t =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom "_ ~> _"]; List (List [vl; body] :: _)] ->
    let vl = unwrap_value_with_loc vl |> fst |> unwrap_cref in
    let body =
      let body, _ = unwrap_value_with_loc body in
      unwrap_expr body in
    Proof_spec.Heap.(Assertion.emp |> Assertion.add_heaplet (PointsTo (vl, body)))
  | "CNotation", [_; List[Atom "InConstrEntry"; Atom notation]; _] ->
    failwith @@ Format.sprintf "found unknown notation %s" notation
  | tag, _ -> failwith @@ Format.sprintf "found unhandled assertion tag %s: %a" tag Sexplib.Sexp.pp_hum sexp

let unwrap_spec_arg sexp : spec_arg =
  let open Sexplib.Sexp in
  match unwrap_tagged sexp with
  | "CRef", _ -> `Expr (`Var (unwrap_cref sexp))
  | "CLambdaN", _ ->
    let args, body = unwrap_clambda sexp in
    let body = unwrap_assertion body in
    `Spec (args, body)
  | tag, _ -> failwith @@ "found unhandled expr tag " ^ tag

let unwrap_tac_capp sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "CApp", [fname; args] ->
    let fname = unwrap_value_with_loc fname
                |> fst
                |> unwrap_cref
    in
    let args  =
      unwrap_list args
      |> List.map
        (function [@warning "-8"] List [binding; _] ->
           unwrap_value_with_loc binding
           |> fst
           |> unwrap_spec_arg
        )
    in
    fname, args

let unwrap_tactic_name sexp =
  let tactics = ["xcf"; "xpullpure"; "xapp"; "xdestruct"; "rewrite"; "destruct"; "xmatch_case"; "xmatch"; "xvalemptyarr"; "xalloc"; "xletopaque"; "xvals"; "apply"; "intros"; "sep_split_tuple"; "admitted"; "xseq"] in

  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "KerName", [_; List [_; Atom id]] ->
    (List.find (fun t -> String.prefix ~pre:t id) tactics)

let unwrap_tacalias sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAlias", [args] ->
    let [@warning "-8"] [name; params] = unwrap_list args in
    let name = unwrap_tactic_name name in
    let args = unwrap_list params in
    name, args

let unwrap_prim_tactic sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacApply", args -> "apply", args
  | "TacIntroPattern", args -> "intros", args
  | "TacInductionDestruct", args -> "case", args
  | _ -> failwith "unhandled primitive tactic"

let unwrap_tacatom sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "TacAtom", [tac] ->
    unwrap_prim_tactic tac

let unwrap_xapp sexp =
  let arg = unwrap_tacgeneric_arg sexp in 
  match [@warning "-8"] unwrap_tagged arg with
  | "CRef", _ -> unwrap_cref arg, []
  | "CApp", _  -> unwrap_tac_capp arg
  | _ -> failwith "unhandled xapp argument type"

let get_id sexp =
  match [@warning "-8"] unwrap_list sexp with
  | [Atom "Id"; Atom id] -> id 

let unwrap_elem_ident sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "ElimOnIdent", [binding] ->
    let v, _ = unwrap_value_with_loc binding in
    v |> get_id

let unwrap_destr_id sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [_ ; id] -> unwrap_elem_ident id

let unwrap_eqn sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [binding] ->
    let v, _ = unwrap_value_with_loc binding in
    match [@warning "-8"] unwrap_list v with
    | [_; eqn] -> get_id eqn

let unwrap_intro_naming sexp =
  let open Sexplib.Sexp in
  let [@warning "-8"] v, _ = unwrap_value_with_loc sexp in
  match [@warning "-8"] unwrap_list v with
  | [_;  id] -> match [@warning "-8"] unwrap_list id with
    | [_; id] -> get_id id

let unwrap_intro_namings_or_nil sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [] -> []
  | vars ->
    List.map unwrap_intro_naming vars

let unwrap_intro_or_pattern sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_tagged sexp with
  | "IntroOrPattern", [vars] ->
    let vars = unwrap_list vars in
    List.map unwrap_intro_namings_or_nil vars

let unwrap_vars sexp =
  let open Sexplib.Sexp in
  match [@warning "-8"] unwrap_list sexp with
  | [vars] ->
    let [@warning "-8"] _, [vars] = unwrap_tagged vars in
    let v, _ = unwrap_value_with_loc vars in
    unwrap_intro_or_pattern v


let unwrap_eqn_vars sexp =
  let open Sexplib.Sexp in
  let [@warning "-8"] [eqn; vars] = unwrap_list sexp in
  let eqn = unwrap_eqn eqn in
  let vars = unwrap_vars vars in
  eqn, vars

let unwrap_case sexp =
  let open Sexplib.Sexp in 
  match [@warning "-8"] sexp with
  | [_; _; args] ->
    let [@warning "-8"] [args; _] = unwrap_list args in
    let [@warning "-8"] [args] = unwrap_list args in
    let [@warning "-8"] [destr; eqn_vars; _] = unwrap_list args in
    let destr_id = unwrap_destr_id destr in
    let eqn, vars = unwrap_eqn_vars eqn_vars in
    destr_id, eqn, vars

