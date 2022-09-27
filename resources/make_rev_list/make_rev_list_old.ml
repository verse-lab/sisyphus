open Common

let make_rev_list (ls: 'a list) =
  let (r : 'a list ref) = ref [] in
  let _ = List.iter (fun (x: 'a)  -> r := x :: !r) ls in
  !r
