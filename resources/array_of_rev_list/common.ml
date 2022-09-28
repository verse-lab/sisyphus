let hd (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | (h: 'a) :: _ -> h

let tl (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | _ :: (t: 'a list) -> t

let rec for_downto from down_to f =
  if from = down_to
  then f from
  else if from > down_to then begin
    f from;
    for_downto (from - 1) down_to f
  end else ()
