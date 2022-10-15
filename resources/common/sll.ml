type 'a node =
  | Node of 'a * 'a node ref
  | Nil

type 'a sll = 'a node ref

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
