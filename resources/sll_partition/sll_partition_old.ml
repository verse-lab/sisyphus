open Sll

let sll_partition (p: 'a -> bool) (s: 'a sll) =
  let (sll_yes: 'a sll) = sll_nil () in
  let (sll_no: 'a sll) = sll_nil () in
  let (sll_yes: 'a sll), (sll_no: 'a sll) = sll_fold (fun (node: 'a) ((sll_yes: 'a sll), (sll_no: 'a sll)) ->
      if p node
      then (let (sll_yes: 'a sll) = sll_cons node sll_yes in (sll_yes, sll_no))
      else (let (sll_no: 'a sll) = sll_cons node sll_no in (sll_yes, sll_no))
    ) (sll_yes, sll_no) s in
  let (_: unit) = sll_reverse sll_yes in
  let (_: unit) = sll_reverse sll_no in
  (sll_yes, sll_no)
[@@with_logical_mapping ["pp", "p"; "ls", "s"]]
[@@with_opaque_encoding ["sll", ("Sll.sll_of_list", "Sll.sll_to_list")]]
