  $ ./run_parser.exe array_partition
  OLD:
  let partition (p: func('a -> bool)) (a: 'a array) =
    let (n: int) = Array.length a in
    if n = 0
    then
    let (a_t: 'a array) = Array.of_list [] in
    let (a_f: 'a array) = Array.of_list [] in (a_t, a_f)
    else
    let (left_arr: 'a array) = Array.make n (Array.get a 0) in
    let (right_arr: 'a array) = Array.make n (Array.get a 0) in
    let (li: int ref) = ref 0 in
    let (ri: int ref) = ref 0 in
    let tmp =
    (fun
      (vl: 'a)
      ->
      if p vl
        then let (unused: unit) = Array.set left_arr (! li) vl in incr li
        else let (unused: unit) = Array.set right_arr (! ri) vl in incr ri)
    in
    let (unused: unit) = array_iter tmp a in
    let (left: 'a array) = array_take (! li) left_arr in
    let (right: 'a array) = array_take (! ri) right_arr in (left,
  right)
  NEW:
  let partition (p: func('a -> bool)) (a: 'a array) =
    let (left_ptr: 'a list ref) = ref [] in
    let (right_ptr: 'a list ref) = ref [] in
    let tmp =
    (fun
      (vl: 'a)
      ->
      let (r: bool) = p vl in
        if r
        then := left_ptr (vl :: ! left_ptr)
        else := right_ptr (vl :: ! right_ptr))
    in
    let (unused: unit) = array_iter tmp a in
    let (left_l_rev: 'a list) = ! left_ptr in
    let (left_l: 'a list) = List.rev left_l_rev in
    let (right_l_rev: 'a list) = ! right_ptr in
    let (right_l: 'a list) = List.rev right_l_rev in
    let (left: 'a array) = Array.of_list left_l in
    let (right: 'a array) = Array.of_list right_l in (left,
  right)
