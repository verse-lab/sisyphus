open Sll

(* functional version of sll_reverse, returns a new SLL *)
let sll_reverse_f (lst: 'a sll) =
  let (rlst: 'a sll) = sll_nil () in
  let (_ : unit) = sll_iter (fun (vl: 'a) ->
      let (_: unit) = sll_push vl rlst in
      ()
    ) lst in
  rlst
