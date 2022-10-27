open Arr
open Sll

let sll_of_array (a: 'a array) =
  let (s: 'a sll) = sll_nil () in
  let (_: unit) = array_iter (fun (v: 'a) ->
    let (_: unit) = Sll.sll_push v s in
    ()
  ) a in
  let (_: unit) = Sll.sll_reverse s in
  s
[@@with_opaque_encoding ["sll", ("Sll.sll_of_list", "Sll.sll_to_list")]]

