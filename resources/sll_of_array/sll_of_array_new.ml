open Combinators
open Sll

let sll_of_array (arr: 'a array) =
  let (ls: 'a sll) = sll_nil () in
  let (len: int) = Array.length arr in
  let (_: unit) = for_downto (len - 1) 0 (fun (i: int) ->
    let (elt: 'a) = arr.(i) in
    let (_: unit) = Sll.sll_push elt ls in
    ()
  ) in
  ls
