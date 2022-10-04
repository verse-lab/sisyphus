
let rec while_upto (start: int) (stop: int) (f: int -> bool) : bool =
  if start = stop
  then true
  else if not (f start)
  then false
  else while_upto (start + 1) stop f
