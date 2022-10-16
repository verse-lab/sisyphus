open Set

let set_to_list (s: set) =
  let (l: int list ref) = ref [] in
  set_iter (fun (e: int) ->
    l := e :: !l;
    ()
  ) s;
  let res = List.rev !l in
  res

