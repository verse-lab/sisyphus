open Common

let set_to_list s =
  StringSet.fold (fun x acc -> x :: acc) ss []
