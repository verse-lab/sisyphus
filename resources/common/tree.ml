type 'a tree =
  | Leaf of 'a
  | Node of 'a * 'a tree * 'a tree

let to_list (t: 'a tree) : 'a list =
  let rec loop acc t =
    match t with
    | Leaf vl ->  vl :: acc
    | Node (vl, t1, t2) ->
      let acc1 = loop acc t1 in
      loop (vl :: acc1) t2
  in
  List.rev (loop [] t)

let rec of_list (ls: 'a list) : 'a tree =
  match ls with
  | [] -> assert false
  | h :: [] | h :: _ :: []-> Leaf h
  | h :: h' :: h'' :: t ->
    begin match (List.length t mod 3) with
    | 0 | 1 -> Node (h, of_list (h' :: t), Leaf h'')
    | 2 -> Node (h, Leaf h', of_list (h'' :: t))
    | _ -> assert false
    end

let rec size t =
  match t with
  | Leaf _ -> 1
  | Node (_, t1, t2) -> 1 + size t1 + size t2

let head t =
  match t with
  | Leaf v -> v
  | Node (v, _, _) -> v

let rec tree_iter f t =
  match t with
  | Leaf v -> f v
  | Node (v, t1, t2) ->
    tree_iter f t1;
    f v;
    tree_iter f t2

let rec tree_fold f acc t =
  match t with
  | Leaf v -> f acc v
  | Node (v, t1, t2) ->
    let a1 = tree_fold f acc t1 in
    let a2 = f a1 v in
    let a3 = tree_fold f a2 t2  in
    a3
