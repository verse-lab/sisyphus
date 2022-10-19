open Sll

(* functional version of sll_reverse, returns a new SLL *)
let sll_reverse_f (lst: 'a sll) =
  let (init: 'a sll) = sll_nil () in
  let (rlst : 'a sll) = sll_fold (fun (vl: 'a) (lst: 'a sll) ->
      let (rlst: 'a sll) = sll_cons vl lst in
      rlst
    ) init lst in
  rlst
