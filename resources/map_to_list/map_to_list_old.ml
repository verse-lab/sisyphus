open Common

let to_list map =
  let list = ref [] in
  StringMap.iter (fun x y -> list := (x,y) :: !list) map;
  List.rev !list
