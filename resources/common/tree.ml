type 'a tree =
  | Leaf
  | Node of 'a * 'a tree * 'a tree

let rec tree_iter f t =
  match t with
  | Leaf -> ()
  | Node (v, t1, t2) -> tree_iter f t1; f v; tree_iter f t2

let rec tree_fold f t acc =
  match t with
  | Leaf -> acc
  | Node (v, t1, t2) ->
    let a1 = tree_fold f t1 acc in
    let a2 = f v a1 in
    let a3 = tree_fold f t2 a2 in
    a3
