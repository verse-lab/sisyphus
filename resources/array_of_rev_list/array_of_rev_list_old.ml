open Common

let array_of_rev_list (l: 'a list) =
  match l with
  |  [] -> [| |]
  | (x: 'a) :: (t: 'a list) ->
    let (len: int) = List.length l in
    let (a: 'a array) = Array.make len x in
    let (r: 'a list ref) = ref t in
    let _ =
      for_downto (len - 2) 0 (fun (i: int) ->
        let _ = a.(i) <- hd !r in
        let _ = r := tl !r in
        ()
      ) in
    a
