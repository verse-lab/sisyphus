type 'a node =
  | Node of 'a * 'a node ref
  | Nil

type 'a sll = 'a node ref

let sll_cons_unfold (ls: 'a sll) : 'a sll = match !ls with
  | Node (_, tl) -> tl
  | _ -> assert false

let sll_cons (hd: 'a) (tl: 'a sll) : 'a sll = ref (Node (hd, tl))

let sll_nil () : 'a sll =
  let (res : 'a sll) = ref (Nil : 'a node) in
  res

let sll_push (hd: 'a) (ls: 'a sll) : unit =
  let (tl: 'a node) = !ls in
  let (new_tl: 'a sll) = ref tl in
  ls := Node (hd, new_tl)

let rec sll_of_list (ls: 'a list) : 'a sll =  match ls with
  | [] -> sll_nil ()
  | h :: t -> sll_cons h (sll_of_list t)

let rec sll_to_list (ls: 'a sll) : 'a list =  match !ls with
  | Nil -> []
  | Node (h, t) -> h  :: sll_to_list t

let sll_iter (f: 'a -> unit) (lst: 'a sll) =
  let rec aux node =
    match !node with
    | Nil -> ()
    | Node (hd, tl) -> begin
        f hd;
        aux tl
      end in
  let res = aux lst in
  res

let sll_iter_drain (f: 'a -> unit) (lst: 'a sll) =
  let rec aux () =
    match !lst with
    | Nil -> ()
    | Node (hd, tl) ->
      f hd;
      lst := !tl;
      aux () in
  aux ()

let sll_fold (f: 'a -> 'b -> 'b) (init: 'b) (lst: 'a sll) =
  let rec aux node acc =
    match !node with
    | Nil -> acc
    | Node (hd, tl) ->
      let acc = f hd acc in
      aux tl acc in
  aux lst init

let sll_reverse (ls : 'a sll) : unit =
  let rec loop (el: 'a sll) : 'a sll =
    let node = !el in
    match node with
    | Nil -> el
    | Node (hd, tl) ->
      let last = loop tl in
      let new_last = ref Nil in
      last := Node (hd, new_last);
      el := !tl;
      new_last in
  let _ = loop ls in
  ()
      
