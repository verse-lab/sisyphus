open Common

let array_of_rev_list l =
  match l with
    [] -> [| |]
  | x :: tl ->
    let len = List.length l in
    let a = Array.make len x in
    let r = ref tl in
    for i = len - 2 downto 0 do
      let hd,tl = match !r with hd :: tl -> (hd,tl) | _ -> assert false in
      a.(i) <- hd;
      r := tl;
    done;
    a
