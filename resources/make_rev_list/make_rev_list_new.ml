open Common

let make_rev_list (ls: 'a list) =
  let (result: 'a list) =
    List.fold_left
      (fun (acc: 'a list) (x: 'a)  -> x :: acc)
      [] ls in
  result
