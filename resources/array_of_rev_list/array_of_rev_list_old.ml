open Common

let array_of_rev_list (l: 'a list) =
  match l with
  |  [] -> [| |]
  | (x: 'a) :: (t: 'a list) ->
    let (len: int) = List.length l in
    let (a: 'a array) = Array.make len x in
    let (r: 'a list ref) = ref t in
    let rec loop (i: int) =
      if i >= 0 then begin
        let _ = a.(i) <- hd !r in
        let _ = r := tl !r in
        loop (i - 1)
      end else ()
    in
    let _ = loop (len - 2) in
    a
