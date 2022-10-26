open Tree

let tree_to_array (tree: 'a tree[@collection Tree.of_list, Tree.to_list])  =
  let (len: int) = size tree in
  let (head: 'a) = Tree.head tree in
  let (arr: 'a array) = Array.make len head in
  let (i: int ref) = ref 0 in
  let (_: unit) = tree_iter (fun (vl: 'a) ->
      arr.(!i) <- vl;
      let (_: unit) = incr i in
      ()
  ) tree in
  arr
