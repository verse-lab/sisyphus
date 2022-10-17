open Combinators
open Sll

let sll_of_array (arr: 'a array) =
  let (ls: 'a sll) = sll_nil () in
  let (len: int) = Array.length arr in
  let _ = for_downto (len - 1) 0 (fun i ->
    let elt = arr.(i) in
    Sll.sll_push elt ls
  ) in
  ls
