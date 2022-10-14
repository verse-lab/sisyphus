open Arr

let foldi (t: 'a array) (init: 'b) (f: int -> 'a -> 'b -> 'b) =
  let (acc: 'b ref) = ref init in
  array_iteri (fun (i: int) (x: 'a) -> 
    acc := f i x !acc
  ) t;
  let (res: 'b) = !acc in
  res
