open Common

let array_of_rev_list l =
  match l with
    [] -> [| |]
  | x :: l' ->
    let len = List.length l in
    let a = Array.make len x in
    let r = ref l' in
    for i = len - 2 downto 0 do
      a.(i) <- hd !r;
      r := tl !r
    done;
    a
