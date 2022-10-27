open Tree

let tree_to_array (t: 'a tree[@collection Tree.tree_of_list, Tree.tree_to_list]) =
  let (head: 'a) = Tree.tree_head t in
  let ((len: int), (elts: 'a list)) =
    tree_fold (fun ((i: int), (acc: 'a list)) (vl: 'a) -> (i + 1, vl :: acc)) (0, []) t in
  let (arr: 'a array) = Array.make len head in
  let (idx: int) = len - 1 in
  let (_: int) =
    List.fold_left
      (fun (i: int) (vl: 'a) ->
         arr.(i) <- vl;
         i - 1) idx
      elts in
  arr
