  $ ./run_parser.exe sll_partition
  OLD:
  let sll_partition (p: func('a -> bool)) (lst: ('a) sll) =
    let (sll_yes: ('a) sll) = sll_nil () in
    let (sll_no: ('a) sll) = sll_nil () in
    let tmp =
    (fun
      (node: 'a) ((sll_yes: ('a) sll), (sll_no: ('a) sll))
      ->
      if p node
        then
        let (sll_yes: ('a) sll) = sll_cons node sll_yes in
        (sll_yes, sll_no)
        else let (sll_no: ('a) sll) = sll_cons node sll_no in (sll_yes,
  sll_no))
    in
    let ((sll_yes: ('a) sll), (sll_no: ('a) sll)) =
      sll_fold tmp (sll_yes, sll_no) lst
    in
    let (unused: unit) = sll_reverse sll_yes in
    let (unused: unit) = sll_reverse sll_no in (sll_yes, sll_no)
  NEW:
  let
  sll_partition (p: func('a -> bool)) (lst: ('a) sll) =
    let (unused: unit) = sll_reverse lst in
    let (sll_yes: ('a) sll) = sll_nil () in
    let (sll_no: ('a) sll) = sll_nil () in
    let tmp =
    (fun
      (node: 'a)
      ->
      if p node
        then let (unused: unit) = sll_push node sll_yes in ()
        else let (unused: unit) = sll_push node sll_no in ())
    in
    let (unused: unit) = sll_iter tmp lst in (sll_yes,
  sll_no)
