  $ ./run_parser.exe array_exists
  OLD:
  let array_exists (t: 'a array) (f: func('a -> bool)) =
    let (len: int) = Array.length t in
    let (result: bool ref) = ref false in
    let tmp =
    (fun
      (i: int)
      ->
      result := f (Array.get t i);
        not (! result))
    in
    let (unused: bool) = while_upto 0 len tmp in
    let (res: bool) = ! result in res
  NEW:
  let array_exists (a: 'a array) (f:
  func('a -> bool)) =
    let (len: int) = Array.length a in
    let tmp =
    (fun
      (i: int)
      ->
      if f (Array.get a i) then Some true else None)
    in
    let (res: (bool) option) = until_upto 0 len tmp in
    let (res: bool) = Opt.option_is_some res in
  res
