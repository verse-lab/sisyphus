open Common

let array_of_rev_list l =
  match l with
    [] -> [| |]
  | x :: l' ->
    let len = List.length l in
    let a = Array.make len x in
    let r = ref l' in
    let rec loop i =
      if i >= 0 then begin
        a.(i) <- hd !r;
        r := tl !r;
        loop (i - 1)
      end
    in
    loop (len - 2);
    a
