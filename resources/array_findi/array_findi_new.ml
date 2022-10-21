open Combinators

let findi (a: 'a array) (f: int -> 'a -> bool) =
  let (length: int) = Array.length a in
  if length = 0
  then None
  else begin
    let (found: bool ref) = ref false in
    let (idx: int ref) = ref 0 in
    let (first_elt: 'a) = a.(0) in
    let (value: 'a ref) = ref first_elt in
    let _ = while_upto 0 length (fun (i: int) ->
      if f i a.(i) then begin
        idx := i;
        let (ith_elt: 'a) = a.(i) in
        value := ith_elt;
        found := true;
        false
      end else true
    ) in
    if !found
    then
      let (found_index: int) = !idx in
      let (found_value: 'a) = !value in
      Some (found_index, found_value)
    else None
  end
