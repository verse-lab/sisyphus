open Arr
open Sll

let sll_of_array (arr: 'a array) =
  let (ls: 'a sll) = sll_nil () in
  let (_: unit) = array_iter (fun (v: 'a) ->
    let (_: unit) = Sll.sll_push v ls in
    ()
  ) arr in
  let (_: unit) = sll_reverse ls in
  ls
