type 'a t = unit -> 'a node
and 'a node = Nil | Cons of 'a * 'a t
[@@listgen of_list]

let rec of_list ls () = match ls with
  | [] ->  Nil
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

let to_array (l: 'a t) =
  match l () with
  | Nil -> [| |]
  | Cons ((x: 'a), (_unused: 'a t)) ->
    let (n: int) = length' l in
    let (a: 'a array) = Array.make n x in (* need first elem to create [a] *)
    iteri
      (fun (i: int) (x: 'a) -> a.(i) <- x)
      l;
    a

let to_array (l: 'a t) =
  let (len: int), (ls : 'a list) = fold (fun ((i: int), (acc: 'a list)) (x: 'a) -> (i + 1, x :: acc)) (0, []) l in
   match ls with
     | [] -> [| |]
     | (::) ((init: 'a), (rest: 'a list)) ->
       let (a : 'a array) = Array.make len init in
       (* intros arr, data, Hdata *)
       let (idx : int) = len - 2 in
       let _ = List.fold_left (fun (i: int) (x: 'a) -> a.(i) <- x; i - 1) idx rest in
       a
