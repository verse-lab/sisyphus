  $ ./run_parser.exe find_mapi
  OLD:
  let find_mapi (a: 'a array) (f: func(int -> 'a -> ('b) option)) =
    let (len: int) = Array.length a in
    let tmp = (fun (i: int) -> f i (Array.get a i)) in
    let (res: ('b) option) = until_upto 0 len tmp in res
  NEW:
  let find_mapi (a:
  'a array) (f: func(int -> 'a -> ('b) option)) =
    let (len: int) = Array.length a in
    if len = 0
    then None
    else
    let (value_found: ('b) option ref) = ref None in
    let tmp =
    (fun
      (i: int)
      ->
      let (res: ('b) option) = f i (Array.get a i) in
        let (found: bool) = Opt.option_is_some res in
        if found then := value_found res; let (res: bool) = not found in res)
    in
    let (unused: bool) = while_upto 0 len tmp in
    let (res: ('b) option) = ! value_found in
  res
