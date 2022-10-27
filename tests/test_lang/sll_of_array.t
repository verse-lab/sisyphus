  $ ./run_parser.exe sll_of_array
  OLD:
  let sll_of_array (a: 'a array) =
    let (s: ('a) sll) = sll_nil () in
    let (len: int) = Array.length a in
    let tmp =
    (fun
      (i: int)
      ->
      let (elt: 'a) = Array.get a i in
        let (unused: unit) = Sll.sll_push elt s in ())
    in
    let (unused: unit) = for_downto (len - 1) 0 tmp in s
  NEW:
  let sll_of_array
  (a: 'a array) =
    let (s: ('a) sll) = sll_nil () in
    let tmp =
    (fun
      (v: 'a)
      ->
      let (unused: unit) = Sll.sll_push v s in
        ())
    in
    let (unused: unit) = array_iter tmp a in
    let (unused: unit) = Sll.sll_reverse s in
  s
