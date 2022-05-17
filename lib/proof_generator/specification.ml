open Containers
module StringMap = Map.Make(String)

type expr = Lang.Expr.t
type holy_expr = expr -> expr
type ty = Lang.Type.t
type 'a map = 'a StringMap.t

let pp_expr = Lang.Expr.pp
let pp_ty = Lang.Type.pp
let pp_holy_expr fmt v =
  pp_expr fmt (v (`Var "??"))
let pp_map f fmt vl =
  StringMap.pp
    ~pp_start:(fun fmt () -> Format.fprintf fmt "{")
    ~pp_stop:(fun fmt () -> Format.fprintf fmt "}")
    ~pp_arrow:(fun fmt () -> Format.fprintf fmt " -> ")
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ")
    Format.pp_print_string
    f fmt vl
    
type 'a condition = {
  quantified_over: (string * ty) list; (* list of variables being quantified over *)
  assumptions: (expr * expr) list;     (* list of assumed equalities *)
  goal: 'a;                             (* expression to be proved *)
} [@@deriving show]

type initial_vc = {
  assumptions: (expr * expr) list; (* assumptions *)
  expr_values: expr array; (* values for variables *)
  param_values: expr map;  (* initial values for invariant parameters *)
} [@@deriving show]

type vc = {
  qf: (string * ty) list;

  param_values: expr map;
  assumptions: (expr * expr) list;

  post_param_values: expr map;
  expr_values: holy_expr array;
} [@@deriving show]

type verification_condition = {
  initial: initial_vc;
  conditions: vc list;
} [@@deriving show]


let build_verification_condition (t: Proof_context.t) : verification_condition =
  List.iter (fun (name, o_vl, vl) ->
    let name = (List.map Names.Id.to_string name |> String.concat ".") in
    (* Format.printf "hyp: %s[%s] (%s) : %s @."
     *   (List.map Names.Id.to_string name |> String.concat ".")
     *   Proof_debug.(tag vl)
     *   (ostr Proof_debug.constr_to_string_pretty @@ o_vl)
     *   (Proof_debug.constr_to_string_pretty vl); *)

    let is_coq_eq fn = String.(Constr.destInd fn |> fst |> fst |> Names.MutInd.label |> Names.Label.to_string = "eq") in
    begin match Constr.kind vl with

    | Constr.Sort _ ->
      (* represents things like A: Type *)
      ()
    | Constr.App (fn, [| ty; l; r |])
      when Constr.isInd fn && is_coq_eq fn ->
      Format.printf "found %s: %s =(%s) %s@." name
      Proof_debug.(constr_to_string_pretty l)
      Proof_debug.(constr_to_string_pretty ty)
      Proof_debug.(constr_to_string_pretty r)

    | Constr.App (fn, args) ->
      
      Format.printf "found %s[%s](%d): %s.... =====> %s[%s]@." name
        Proof_debug.(tag fn)
        (Array.length args)
      Proof_debug.(constr_to_string fn)
      Proof_debug.(constr_to_string_pretty fn)
      (Array.to_string Proof_debug.constr_to_string_pretty args)
      
      (* list A, and eq, and others *)
    | Constr.Ind _              (* credits? *)
    | Constr.Var _              (* init: A *)
    | Constr.Const _ -> ()
    | _ ->
      Format.printf "ignoring %s[%s]: %s@." name (Proof_debug.tag vl) (Proof_debug.constr_to_string_pretty vl);
    end
  ) (Proof_context.current_goal t).hyp;
  assert false
