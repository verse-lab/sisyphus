type +'a t = unit -> 'a node
and +'a node =
  | Nil
  | Cons of 'a * 'a t

let to_list f =
  let rec loop acc f =
    match f () with
    | Nil -> List.rev acc
    | Cons (h, f) -> loop (h :: acc) f in
  loop [] f

let rec int_range fro toe : int t =
  fun () ->
  if toe > 0
  then
    let rest = int_range (fro + 1) (toe - 1) in
    Cons (fro, rest)
  else Nil
  
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

let to_array l =
   let len, ls = fold (fun (i, acc) x -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | init::rest ->
       let a = Array.make len init in
       (* Subtract 1 for len->index conversion and 1 for the removed [init] *)
       let idx = len - 2 in
       let _ = List.fold_left (fun i x -> a.(i) <- x; i - 1) idx rest in
       a
