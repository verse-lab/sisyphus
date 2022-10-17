  $ ./run_parser.exe array_of_rev_list
  OLD:
  let array_of_rev_list (l: 'a list) =
    match l with
    | [] -> [| |]
    | (x: 'a) :: (t: 'a list) ->
      let (len: int) = List.length l in
      let (a: 'a array) = Array.make len x in
      let (r: 'a list ref) = ref t in
      let tmp =
      (fun
        (i: int)
        ->
        let (unused: unit) = Array.set a i (hd (! r)) in
          let (unused: unit) = := r (tl (! r)) in ())
      in
      let (unused: unit) = for_downto (len - 2) 0 tmp in a
  NEW:
  let
  array_of_rev_list (l: 'a list) =
    match l with
    | [] -> [| |]
    | (x: 'a) :: (_unused: 'a list) ->
      let (len: int) = List.length l in
      let (a: 'a array) = Array.make len x in
      let tmp = (fun (i: int) (x: 'a) -> Array.set a (len - 1 - i) x) in
      let (unused: unit) = List.iteri tmp l in
  a
