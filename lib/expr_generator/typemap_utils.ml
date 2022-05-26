open Containers

let update_binding env ty vl =
  Expgen.TypeMap.update ty
    (fun v ->
       Option.value ~default:[] v
       |> List.cons vl
       |> Option.some)
    env


let get_consts_type_map  consts_in_script ints vars =
  let ints = Expgen.TypeMap.of_list ints in
  let consts = List.fold_left
      (fun acc x ->
         match x with
           `Int i -> update_binding acc Int (`Int i)
         | _ -> acc
      ) ints
      consts_in_script
  in
  let consts = List.fold_left (fun acc (vname, ty) ->
      update_binding acc ty (`Var vname)
    ) consts vars
  in
  consts

let get_consts_and_funcs steps ~from_id ~to_id ~env ~ints ~vars ~funcs=
  let open Lang.Type in
  let consts_in_script =  Collector.collect_constants from_id to_id steps in
  let consts = get_consts_type_map consts_in_script ints vars in

  let handle_funcs env consts =
    let open Expgen in
    let add_to_map map = function
      | `Func fname ->
        let input_types, ret_type = env fname in
        let ty = fname, input_types in
        TypeMap.update ret_type (function Some ls -> Some (ty :: ls) | None -> Some [ty]) map
      | _ -> map
    in

    let init = TypeMap.of_list funcs in
    List.fold_left add_to_map init consts
  in

  consts, handle_funcs env consts_in_script

let get_pats steps env =
  let pats = Patgen.pat_gen env steps in
  Patgen.get_pat_type_map env pats

