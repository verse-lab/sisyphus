  $ ./run_parser.exe array_is_sorted
  OLD:
  let array_is_sorted (t: int array) =
    let (len: int) = Array.length t in
    if len = 0
    then true
    else
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: int) = Array.get t i in
        let (prev_elt: int) = Array.get t (i - 1) in
        if <= prev_elt elt then None else Some ())
    in
    let (res: (() unit) option) = until_downto (len - 1) 0 tmp in
    let (res: bool) = Opt.option_is_some res in not res
  NEW:
  let
  array_is_sorted (t: int array) =
    let (len: int) = Array.length t in
    if len = 0
    then true
    else
    let (result: bool ref) = ref true in
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: int) = Array.get t i in
        let (prev_elt: int) = Array.get t (i - 1) in
        if > prev_elt elt then := result false; ! result)
    in
    let (unused: unit) = while_downto (len - 1) 0 tmp in
    let (res: bool) = ! result in
  res
