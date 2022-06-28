open Common

let make_rev_list ls =
  let r = ref [] in
  List.iter (fun x -> r := x :: !r) ls;
  !r
