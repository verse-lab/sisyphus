  $ ./run_parser.exe make_rev_list
  OLD:
  let make_rev_list (ls: 'a list) =
    let (r: 'a list ref) = ref [] in
    let tmp = (fun (x: 'a) -> := r (x :: ! r)) in
    let (unused: unit) = List.iter tmp ls in ! r
  NEW:
  let make_rev_list (ls: 'a
  list) =
    let tmp = (fun (acc: 'a list) (x: 'a) -> x :: acc) in
    let (result: 'a list) = List.fold_left tmp [] ls in
  result
