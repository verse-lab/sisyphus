  $ ./run_parser.exe set_to_list
  OLD:
  let set_to_list (s: () set) =
    let (l: int list ref) = ref [] in
    let tmp = (fun (e: int) -> l := e :: ! l; ()) in
    let (unused: unit) = set_iter tmp s in
    let (res: int list) = List.rev (! l) in res
  NEW:
  let set_to_list (s: ()
  set) =
    let tmp = (fun (acc: int list) (x: int) -> x :: acc) in
    let (res: int list) = set_fold tmp [] s in
    let (res: int list) = List.rev res in
  res
