  $ ./run_parser.exe sll_of_array
  OLD:
  let sll_of_array (arr: 'a array) =
    let (ls: ('a) sll) = sll_nil () in
    let tmp =
    (fun
      (v: 'a)
      ->
      let (unused: () unit) = Sll.sll_push v ls in
        ())
    in
    let (unused: () unit) = array_iter tmp arr in
    let (unused: () unit) = sll_reverse ls in ls
  NEW:
  let sll_of_array (arr: 'a
  array) =
    let (ls: ('a) sll) = sll_nil () in
    let (len: int) = Array.length arr in
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: 'a) = Array.get arr i in
        let (unused: () unit) = Sll.sll_push elt ls in ())
    in
    let (unused: () unit) = for_downto (len - 1) 0 tmp in
  ls
