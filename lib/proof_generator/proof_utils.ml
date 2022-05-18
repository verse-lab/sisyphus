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
