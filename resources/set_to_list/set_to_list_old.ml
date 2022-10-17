open Set

let set_to_list (s: set) =
  let (l: int list ref) = ref [] in
  let (_: unit) = set_iter (fun (e: int) ->
    l := e :: !l;
    ()
  ) s in
  let (res: int list) = List.rev !l in
  res

