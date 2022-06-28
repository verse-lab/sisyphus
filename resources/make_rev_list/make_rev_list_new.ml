open Common

let make_rev_list ls =
  List.fold_left (fun acc x -> x :: acc) ls
