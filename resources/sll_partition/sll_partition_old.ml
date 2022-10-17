open Sll

let sll_partition (p: 'a -> bool) (lst: 'a sll) =
  let (sll_yes: 'a sll) = sll_nil () in
  let (sll_no: 'a sll) = sll_nil () in
  let (sll_yes: 'a sll), (sll_no: 'a sll) = sll_fold (fun node (sll_yes, sll_no) ->
      if p node
      then (let sll_yes = sll_cons node sll_yes in (sll_yes, sll_no))
      else (let sll_no = sll_cons node sll_no in (sll_yes, sll_no))
    ) (sll_yes, sll_no) lst in
  let (_: unit) = sll_reverse sll_yes in
  let (_: unit) = sll_reverse sll_no in
  (sll_yes, sll_no)
