open Combinators
open Sll

let sll_of_array (a: 'a array) =
  let (s: 'a sll) = sll_nil () in
  let (len: int) = Array.length a in
  let (_: unit) = for_downto (len - 1) 0 (fun (i: int) ->
    let (elt: 'a) = a.(i) in
    let (_: unit) = Sll.sll_push elt s in
    ()
  ) in
  s
[@@with_opaque_encoding ["sll", ("Sll.sll_of_list", "Sll.sll_to_list")]]
