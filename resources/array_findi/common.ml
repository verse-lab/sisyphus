
let rec until_upto start stop f =
  if start = stop
  then None
  else match f start with
    | Some v -> Some v
    | None ->
      until_upto (start + 1) stop f

let rec while_upto (start: int) (stop: int) (f: int -> bool) : bool =
  if start = stop
  then true
  else if not (f start)
  then false
  else while_upto (start + 1) stop f
