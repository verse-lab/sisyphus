open Tree

let tree_to_array (t: 'a tree) =
  let (len: int) = tree_size t in
  let (head: 'a) = Tree.tree_head t in
  let (arr: 'a array) = Array.make len head in
  let (i: int ref) = ref 0 in
  let (_: unit) = tree_iter (fun (vl: 'a) ->
      let (i_vl: int) = !i in 
      arr.(i_vl) <- vl;
      let (_: unit) = incr i in
      ()
  ) t in
  arr
[@@with_logical_mapping ["t", "t"]]
[@@with_opaque_encoding ["tree", ("Tree.tree_of_list", "Tree.tree_to_list")]]
