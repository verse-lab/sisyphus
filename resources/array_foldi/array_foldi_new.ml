open Arr

let foldi (t: 'a array) (init: 'b) (f: int -> 'a -> 'b -> 'b) =
  let (acc: 'b ref) = ref init in
  let (_: unit) = array_iteri (fun (i: int) (x: 'a) -> 
    acc := f i x !acc;
    ()
  ) t in
  let (res: 'b) = !acc in
  res
