open Combinators

let findi (t: 'a array) (f: int -> 'a -> bool) =
  let (length: int) = Array.length t in
  if length = 0
  then None
  else begin
    let (found: bool ref) = ref false in
    let (idx: int ref) = ref 0 in
    let (value: 'a ref) = ref t.(0) in
    let _ = while_upto 0 length (fun (i: int) ->
      if f i t.(i) then begin
        idx := i;
        value := t.(i);
        found := true;
        false
      end else true
    ) in
    if !found
    then Some (!idx, !value)
    else None
  end
