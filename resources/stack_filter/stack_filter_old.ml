open Stack

let stack_filter (f: 'a -> bool) (s: 'a stack) =
  let (acc: 'a list ref) = ref [] in
  let (_: unit) =
    stack_iter
      (fun (vl: 'a) ->
         if f vl then
           (acc := vl :: !acc; ());
         ()
      ) s in
  let (_: unit) = stack_clear s in
  let (elts: 'a list) = !acc in
  let (_: unit) = List.iter (fun (vl: 'a) ->
    stack_push s vl
  ) elts in
  ()
