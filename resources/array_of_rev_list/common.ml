let hd (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | (h: 'a) :: _ -> h

let tl (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | _ :: (t: 'a list) -> t
