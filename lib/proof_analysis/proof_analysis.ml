open Containers

type t = Lol

(** [is_const_wp_fn cst] determines whether a {!Constr.t} term
   represents a constant weakest precondition helper. *)
let is_const_wp_fn cst =
  Constr.isConst cst && begin
    let cst, _ = Constr.destConst cst  in
    String.suffix ~suf:"_cf__" @@  Names.Constant.to_string cst
  end

let rec extract_fold_specification (wp: Constr.t) : t  =

  Format.ksprintf ~f:failwith
    "extract_fold_specification received %s"
    (Proof_utils.Debug.constr_to_string wp)

  
let analyse (trm: Constr.t) : t =
  match Constr.kind trm with
  | Constr.App (trm, args) when is_const_wp_fn trm && Array.length args > 0 ->
    let _initial_args = 
      Array.to_iter args |> Iter.find_map (fun trm ->
        match Constr.kind trm with
        | Constr.App (trm, args) when Constr.isVar trm ->
          Some args
        | _ ->
          None
      ) in
    let wp = args.(Array.length args - 1) in

    let _fspec = extract_fold_specification wp in

    failwith "lol"
  | _ -> 
    failwith ("lol " ^ Proof_utils.Debug.tag trm)
  
