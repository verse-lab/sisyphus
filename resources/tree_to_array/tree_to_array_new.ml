open Tree
open Lst

let tree_to_array (tree: 'a tree[@collection Tree.of_list, Tree.to_list]) =
  let (len: int ref) = ref 0 in
  let (elts: 'a list) =
    tree_fold (fun (acc: 'a list) (vl: 'a) ->
        let _ = incr len in
        vl :: acc)
      [] tree in
  let (head: 'a) = hd elts in
  let (arr: 'a array) =
    Array.make !len head in
  let (_: int) =
    List.fold_left
      (fun (i: int) (vl: 'a) ->
         arr.(i) <- vl;
         i - 1)
      (!len - 2)
      (tl elts) in
  arr
