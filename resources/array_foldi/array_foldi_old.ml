open Combinators


let foldi (t: 'a array) (init: 'b) (f: int -> 'a -> 'b -> 'b) =
  let (len: int) = Array.length t in 
  let (res: 'b) =
    nat_fold_up 0 len
     (fun (i: int) (acc: 'b) -> 
       f i t.(i) acc)
     init in
  res
