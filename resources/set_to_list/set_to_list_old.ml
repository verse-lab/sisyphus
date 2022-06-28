open Common

let set_to_list s =
  let l = ref [] in
  StringSet.iter (fun e -> l := e :: !l) s;
  !l
