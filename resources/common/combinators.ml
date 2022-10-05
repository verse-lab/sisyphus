let rec for_upto from upto f =
  if from = upto
  then f from
  else if from < upto then begin
    f from;
    for_upto (from + 1) upto f
  end else ()

let rec for_downto from down_to f =
  if from = down_to
  then f from
  else if from > down_to then begin
    f from;
    for_downto (from - 1) down_to f
  end else ()

let rec until_downto from down_to f ~final =
  if from <= down_to then final else
    match (f from) with
    | None -> until_downto (from - 1) down_to f ~final
    | Some v -> v

let rec until_upto from upto f ~final =
  if from >= upto then final else
    match (f from) with
    | None -> until_upto (from + 1) upto f ~final
    | Some v -> v

let rec while_upto from upto f  =
  if from > upto then ()
  else if f from then while_upto (from + 1) upto f
  else ()

let rec while_downto from down_to f  =
  if from < down_to then ()
  else if f from then while_downto (from - 1) down_to f
  else ()

let nat_fold from upto f init =
  let rec aux i acc =
    if i = upto then acc
    else aux (i + 1) (f i acc)
  in
  aux from init



(* let foldi f init t = *)
(*   let acc = ref init in *)
(*   array_iteri (fun i x -> acc := f i t.(i) !acc) init t; *)
(*   !acc *)

(* let array_is_sorted t cmp = *)
(*   let len = Array.length t in *)
(*   until_downto (len - 1) 0 (fun i -> *)
(*       if cmp t.(i -1) t.(i) > 0 then Some false *)
(*       else None *)
(*     ) ~final:true *)

(* let is_sorted t ~cmp = *)
(*   let len = Array.length t in *)
(*   let result = ref true in *)
(*   while_downto (len - 1) 0 (fun i -> *)
(*       let elt_i = t.(i) in *)
(*       let elt_i_prd = t.(i - 1) in *)
(*       result := cmp elt_i_prd elt_i <= 0; *)
(*       !result *)
(*     ); *)
(*   !result *)

(* let array_map2 f xs ys = *)
(*   let lx = Array.length xs in *)
(*   let zs = *)
(*     Array.make lx *)
(*       (f xs.(0) ys.(0)) in *)
(*   for_upto 0 (lx - 1) (fun i -> *)
(*       zs.(i) <- f xs.(i) ys.(i); *)
(*     ); *)
(*   zs *)

(* let sll_reverse_fold (lst: 'a sll) = *)
(*   let rev_node = fold_sll (fun node acc -> *)
(*       Some { elt = node.elt; next = acc } *)
(*     ) None lst *)
(*   in *)
(*   { head = rev_node } *)

(* let sll_reverse_iter (lst: 'a sll) = *)
(*   let acc = ref None in *)
(*   iter_sll (fun node  -> *)
(*       acc := Some { elt = node.elt; next = !acc } *)
(*     ) lst; *)
(*   { head = !acc } *)

(* let sll_reverse_rec lst = *)
(*   let rec aux (ls: 'a  node option) (acc: 'a node option) = *)
(*     match ls with *)
(*     | None -> acc *)
(*     | Some node -> *)
(*       aux node.next (Some ({ elt = node.elt; next = acc })) *)
(*   in *)
(*   { head = aux lst.head None } *)


(* let sll_partition_fold p lst = *)
(*   let yes, no = fold_sll (fun node (yesdst, nodst) -> *)
(*       if p node.elt *)
(*       then (Some { elt = node.elt; next = yesdst }, nodst) *)
(*       else (yesdst, Some { elt = node.elt; next = nodst}) *)
(*     ) (None, None) lst *)
(*   in *)

(*   let yes, no = {head=yes},{head=no} in *)
(*   (sll_reverse_fold yes, sll_reverse_fold no) *)

(* let sll_partition_iter p lst = *)
(*   let yesdst, nodst = ref None, ref None in *)
(*   iter_sll (fun node -> *)
(*       if p node.elt *)
(*       then yesdst := Some { elt = node.elt; next = !yesdst } *)
(*       else nodst := Some { elt = node.elt; next = !nodst } *)
(*     ) lst; *)

(*   let yes, no = { head = !yesdst }, { head = !nodst} in *)
(*   (sll_reverse_iter yes, sll_reverse_iter no) *)

(* let filter' p v = *)
(*   let j = ref 0 in *)
(*   let n = v.size in *)

(*   for_upto 0 (n - 1) (fun i -> *)
(*       if p v.vec.(i) then ( *)
(*         if i > !j *)
(*           v.vec.(!j) <- v.vec.(i); *)
(*         incr j *)
(*       )); *)
(*   v.size <- !j *)

(* let filter' p v = *)
(*   let i = ref 0 in *)
(*   let j = ref 0 in *)
(*   let n = v.size in *)
(*   while !i < n do *)
(*     if p v.vec.(! i) then ( *)
(*       if !i > !j then *)
(*         v.vec.(!j) <- v.vec.(!i); *)
(*       incr i; *)
(*       incr j *)
(*     ) else incr i *)
(*   done; *)
(*   if !j > 0 && !j < v.size then ( *)
(*     Array.fill v.vec !j (v.size - !j) v.vec.(0); *)
(*   ); *)
(*   v.size <- !j *)
