open Containers
module IntSet = Set.Make(Int)

let get_implicits_for_fun fn =
  Impargs.implicits_of_global (Names.GlobRef.ConstRef fn)
  |> List.concat_map Fun.(List.rev % snd)
  |> List.filter_map (Option.map (fun ((_, id,_), _, _) -> id - 1))
  |> IntSet.of_list

let drop_implicits fn params =
  let implicits = Impargs.implicits_of_global (Names.GlobRef.ConstRef fn) in
  List.rev implicits
  |> List.concat_map Fun.(List.rev % snd)
  |> List.filter_map (Option.map (fun ((_, id,_), _, _) -> id))
  |> List.fold_left (fun ls i -> List.remove_at_idx (i - 1) ls) params


let is_coq_eq fn =
  Constr.isInd fn &&
  String.(Constr.destInd fn |> fst |> fst |> Names.MutInd.label |> Names.Label.to_string = "eq")

let is_ind_eq str fn =
  Constr.isInd fn &&
  String.equal str
    (Constr.destInd fn |> fst |> fst |> Names.MutInd.to_string)

let is_constr_eq str fn =
  Constr.isConstruct fn &&
  String.equal str
    (Constr.destConstruct fn |> fst |> fst |> fst |> Names.MutInd.to_string)

let is_const_eq str fn =
  Constr.isConst fn &&
  String.equal str
    (Constr.destConst fn |> fst |> Names.Constant.to_string)

let is_unnamed_prod (c: Constr.t) =
      Constr.isProd c
      && Constr.destProd c |> (fun (name, _, _) -> name.binder_name)
         |> Names.Name.is_anonymous

let is_constr_cons fn =
  is_constr_eq "Coq.Init.Datatypes.list" fn
  && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_nil fn =
  is_constr_eq "Coq.Init.Datatypes.list" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_unit fn =
  is_constr_eq "Coq.Init.Datatypes.unit" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_option_some fn =
  is_constr_eq "Coq.Init.Datatypes.option" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_option_none fn =
  is_constr_eq "Coq.Init.Datatypes.option" fn
  && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_bool_true fn =
  is_constr_eq "Coq.Init.Datatypes.bool" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_bool_false fn =
  is_constr_eq "Coq.Init.Datatypes.bool" fn
  && (Constr.destConstruct fn |> fst |> snd) = 2


let is_constr_z0 fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_zpos fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
  && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_zneg fn =
  is_constr_eq "Coq.Numbers.BinNums.Z" fn
  && (Constr.destConstruct fn |> fst |> snd) = 3

let is_constr_pos_x0 fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
  && (Constr.destConstruct fn |> fst |> snd) = 2

let is_constr_pos_x1 fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
  && (Constr.destConstruct fn |> fst |> snd) = 1

let is_constr_pos_xh fn =
  is_constr_eq "Coq.Numbers.BinNums.positive" fn
  && (Constr.destConstruct fn |> fst |> snd) = 3

(** [is_eq_refl trm] determines if the proof term [trm] is an instance
   of an eq-refl proof.  *)
let is_eq_refl trm =
  Constr.isApp trm && begin
    let fn, args = Constr.destApp trm in
    Array.length args = 2 &&
    is_constr_eq "Coq.Init.Logic.eq" fn
    && (Constr.destConstruct fn |> fst |> snd) = 1
end

(** [is_case_bool trm] determines if the proof term [trm] is a case on boolean values.  *)
let is_case_bool trm =
  Constr.isCase trm && begin
    let (info, _, case_args, _, _, vl, cases) = Constr.destCase trm in
    Array.length case_args = 0 &&
    Array.length cases = 2 &&
    String.equal (Names.MutInd.to_string (fst info.ci_ind)) "Coq.Init.Datatypes.bool"
end


(** [extract_const_int c] converts a Coq representation of a constant integer to an OCaml integer  *)
let extract_const_int (c: Constr.t) : int =
  let rec extract_int c =
    match Constr.kind c with
    | Constr.App (const, [|inner|]) when is_constr_pos_x0 const ->
      2 * (extract_int inner)
    | Constr.App (const, [|inner|]) when is_constr_pos_x1 const ->
      1 + 2 * (extract_int inner)
    | _ when is_constr_pos_xh c ->
      1
    | _ ->
      Format.ksprintf ~f:failwith "found unhandled Coq term (%s) that could not be converted to a constant int"
        (Proof_debug.constr_to_string c) in
  match Constr.kind c with
  | Constr.App (const, [|inner|]) when is_constr_zpos const ->
    (extract_int inner)
  | Constr.App (const, [|inner|]) when is_constr_zneg const ->
     (- (extract_int inner))
  | Constr.App (const, [| |]) when is_constr_z0 const ->
    0
  | _ -> 
    Format.ksprintf ~f:failwith "found unhandled Coq term (%s) that could not be converted to a constant int expr"
      (Proof_debug.constr_to_string c)

(** [extract_inductive_list c] converts a Coq representation of a list of elements to an OCaml list of Constr.t's  *)
let unwrap_inductive_list (c: Constr.t) =
  let rec loop acc c = 
    match Constr.kind c with
    | Constr.App (const, [|ty; h; tl|]) when is_constr_cons const ->
      loop (h :: acc) tl
    | Constr.App (const, [|ty|]) when is_constr_nil const ->
      List.rev acc
    | _ ->
      Format.ksprintf ~f:failwith "found unhandled Coq term (%s)[%s] in (%s) that could not be converted to a list"
        (Proof_debug.constr_to_string c) (Proof_debug.tag c) (Proof_debug.constr_to_string_pretty c) in
  loop [] c

(** [extract_trm_app trm] when given a Coq term [trm] of the form
   [(<constant> <args...>)] returns [Some <constant>] otherwise
   [None].  *)
let extract_trm_app trm =
  match Constr.kind_nocast trm with
  | Constr.App (f, _) -> begin match Constr.kind_nocast f with
    | Constr.Const (n, _) -> Some n
    | _ -> None
  end
  | _ -> None
