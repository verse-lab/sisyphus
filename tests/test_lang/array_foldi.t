  $ ./run_parser.exe array_foldi
  OLD:
  let foldi (a: 'a array) (init: 'b) (f: func(int -> 'a -> 'b -> 'b)) =
    let (len: int) = Array.length a in
    let tmp = (fun (i: int) (acc: 'b) -> f i (Array.get a i) acc) in
    let (res: 'b) = nat_fold_up 0 len tmp init in res
  NEW:
  let foldi (a: 'a
  array) (init: 'b) (f: func(int -> 'a -> 'b -> 'b)) =
    let (acc: 'b ref) = ref init in
    let tmp = (fun (i: int) (x: 'a) -> acc := f i x (! acc); ()) in
    let (unused: unit) = array_iteri tmp a in let (res: 'b) = ! acc in
  res
