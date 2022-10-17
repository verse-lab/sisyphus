open Sll

let sll_partition (p: 'a -> bool) (lst: 'a sll) =
  let (_: unit) = sll_reverse lst in
  let (sll_yes: 'a sll) = sll_nil () in
  let (sll_no: 'a sll) = sll_nil () in
  let (_: unit) = sll_iter (fun (node: 'a) ->
      if p node
      then (let (_: unit) = sll_push node sll_yes in ())
      else (let (_: unit) = sll_push node sll_no in ())
    ) lst in
  (sll_yes, sll_no)
