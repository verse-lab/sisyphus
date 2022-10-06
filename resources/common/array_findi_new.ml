open Combinators

let findi t f =
  let length = Array.length t in
  if length = 0
  then None
  else begin
    let found = ref false in
    let idx = ref 0 in
    let value = ref t.(0) in
    let _ = while_upto 0 length (fun i ->
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
