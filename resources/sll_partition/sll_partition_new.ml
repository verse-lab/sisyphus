open Sll

let sll_partition (p: 'a -> bool) (s: 'a sll) =
  let (_: unit) = sll_reverse s in
  let (sll_yes: 'a sll) = sll_nil () in
  let (sll_no: 'a sll) = sll_nil () in
  let (_: unit) = sll_iter (fun (node: 'a) ->
      if p node
      then (let (_: unit) = sll_push node sll_yes in ())
      else (let (_: unit) = sll_push node sll_no in ())
    ) s in
  (sll_yes, sll_no)
[@@with_opaque_encoding ["sll", ("Sll.sll_of_list", "Sll.sll_to_list")]]
