type 'a node =
  | Node of 'a * 'a node option ref

type 'a sll = 'a node option

(* let iter_sll (f: 'a node -> unit) lst = *)
(*   let rec aux node = *)
(*     match node with *)
(*     | None -> () *)
(*     | Some node' -> begin *)
(*         f node'; *)
(*         aux node'.next *)
(*       end *)
(*   in *)
(*   aux lst.head *)

(* let fold_sll (f: 'a node -> 'b -> 'b) init lst = *)
(*   let rec aux node acc = *)
(*     match node with *)
(*     | None -> acc *)
(*     | Some node' -> aux node'.next (f node' acc) *)
(*   in *)
(*   aux lst.head init *)
