open Combinators


let foldi (a: 'a array) (init: 'b) (f: int -> 'a -> 'b -> 'b) =
  let (len: int) = Array.length a in 
  let (res: 'b) =
    nat_fold_up 0 len
     (fun (i: int) (acc: 'b) -> 
       f i a.(i) acc)
     init in
  res
[@@with_logical_mapping ["l", "a"; "f", "fp"]]
