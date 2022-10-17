open Arr
open Sll

let sll_of_array (arr: 'a array) =
  let (ls: 'a sll) = sll_nil () in
  array_iter (fun (v: 'a) ->
    Sll.sll_push v ls
  ) arr;
  sll_reverse ls;
  ls
