type 'a tree =
  | Leaf of 'a
  | Node of 'a * 'a tree * 'a tree

let tree_to_list (t: 'a tree) : 'a list =
  let rec loop acc t =
    match t with
    | Leaf vl ->  vl :: acc
    | Node (vl, t1, t2) ->
      let acc1 = loop acc t1 in
      loop (vl :: acc1) t2
  in
  List.rev (loop [] t)

let rec build_tree acc (ls: 'a list) =
  match acc with
  | None -> begin match ls with
    | [] -> None
    | h :: [] -> Some (Leaf h, [])
    | h :: m :: t :: [] -> Some (Node (m, Leaf h, Leaf t), [])
    | h :: t -> build_tree (Some (Leaf h)) t
  end
  | Some tree -> begin match ls with
    | [] -> Some (tree, [])
    | h :: t ->
      begin match build_tree None t with
      | None -> Some (tree, h :: t)
      | Some (new_tree, rest) ->
        build_tree (Some (Node (h, tree, new_tree))) rest
      end
  end

let tree_of_list ls =
  match build_tree None ls with
  | Some (tree, _) -> tree
  | _ -> failwith "invalid argument"

let rec tree_size t =
  match t with
  | Leaf _ -> 1
  | Node (_, t1, t2) -> 1 + tree_size t1 + tree_size t2

let tree_head t =
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
