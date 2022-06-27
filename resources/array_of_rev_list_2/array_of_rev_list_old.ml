open Common

let array_of_rev_list l =
  match l with
    [] -> [| |]
  | x :: tl ->
    let len = List.length l in
    let a = Array.make len x in
    let r = ref tl in
    for i = len - 2 downto 0 do
      a.(i) <- List.hd !r;
      r := List.tl !r
    done;
    a
