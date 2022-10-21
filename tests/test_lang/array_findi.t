  $ ./run_parser.exe array_findi
  OLD:
  let findi (t: 'a array) (f: func(int -> 'a -> bool)) =
    let (len: int) = Array.length t in
    let tmp =
    (fun
      (i: int)
      ->
      if f i (Array.get t i) then Some (i, Array.get t i) else None)
    in
    let (res: ((int * 'a)) option) = until_upto 0 len tmp in res
  NEW:
  let findi
  (t: 'a array) (f: func(int -> 'a -> bool)) =
    let (length: int) = Array.length t in
    if length = 0
    then None
    else
    let (found: bool ref) = ref false in
    let (idx: int ref) = ref 0 in
    let (first_elt: 'a) = Array.get t 0 in
    let (value: 'a ref) = ref first_elt in
    let tmp =
    (fun
      (i: int)
      ->
      if f i (Array.get t i)
        then
        idx := i;
        let (ith_elt: 'a) = Array.get t i in
        value := ith_elt; found := true; false
        else true)
    in
    let (unused: unit) = while_upto 0 length tmp in
    if ! found
    then
    let (found_index: int) = ! idx in
    let (found_value: 'a) = ! value in Some (found_index, found_value)
    else
  None
