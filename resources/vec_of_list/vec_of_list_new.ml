open Common

let of_list l = match l with
  | [] -> create()
  | [x] -> return x
  | [x;y] -> {size=2; vec=[| x; y |]}
  | x::_ ->
    let v = create_with ~capacity:(List.length l) x in
    List.iter (push_unsafe v) l;
    v
