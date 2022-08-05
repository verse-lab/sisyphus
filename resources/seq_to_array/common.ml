type +'a t = unit -> 'a node
and +'a node =
  | Nil
  | Cons of 'a * 'a t

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

let to_list f =
  let rec loop acc f =
    match f () with
    | Nil -> List.rev acc
    | Cons (h, f) -> loop (h :: acc) f in
  loop [] f

let rec of_list ls () =
  match ls with
  | [] -> Nil
  | h :: t -> Cons (h, of_list t)

let rec fold f acc res = match res () with
  | Nil -> acc
  | Cons (s, cont) -> fold f (f acc s) cont

let length' l = fold (fun acc _ -> acc+1) 0 l

let iteri f l =
  let rec aux f l i = match l() with
    | Nil -> ()
    | Cons (x, l') ->
      f i x;
      aux f l' (i+1)
  in
  aux f l 0
