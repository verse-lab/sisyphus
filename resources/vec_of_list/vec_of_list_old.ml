open Common

 let of_list l = match l with
   | [] -> create()
   | x::_ ->
     let v = create_with ~capacity:(List.length l + 5) x in
     List.iter (push_unsafe v) l;
     v
