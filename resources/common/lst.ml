let hd (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | (h: 'a) :: _ -> h

let tl (ls: 'a list) = match ls with
  | [] -> failwith "called hd on empty list"
  | _ :: (t: 'a list) -> t

let rec list_iteri_aux f i ls =
  match ls with
  | [] -> ()
  | h :: t ->
    f i h;
    list_iteri_aux f (i + 1) t

let list_iteri f ls =
  list_iteri_aux f 0 ls

let rec list_make n vl =
  if n <= 0
  then []
  else vl :: list_make (n - 1) vl

let rec list_drop n ls =
  if n <= 0
  then ls
  else match ls with
    | [] -> []
    | _ :: t -> list_drop (n - 1) t

let rec list_take n ls =
  if n <= 0
  then []
  else match ls with
    | [] -> []
    | h :: t -> h :: list_take (n - 1) t

let rec list_sum ls =
  match ls with
  | [] -> 0
  | h :: t -> h + list_sum t
