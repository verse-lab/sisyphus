let rec for_upto from upto f =
  if from = upto
  then ()
  else if from < upto then begin
    f from;
    for_upto (from + 1) upto f
  end else ()

let rec for_downto from down_to f =
  if from = down_to
  then f down_to
  else if from > down_to then begin
    f from;
    for_downto (from - 1) down_to f
  end else ()

let rec until_downto start stop f =
  if start = stop
  then None
  else match f start with
    | Some v -> Some v
    | None ->
      until_downto (start - 1) stop f

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

let rec while_downto (start: int) (stop: int) (f: int -> bool) : bool =
  if start = stop
  then true
  else if not (f start)
  then false
  else while_downto (start - 1) stop f

let nat_fold_up (from: int) (upto: int) (f: int -> 'a -> 'a) (init: 'a) =
  let rec aux i acc =
    if i = upto then acc
    else aux (i + 1) (f i acc)
  in
  aux from init

let nat_fold_down from down f init =
  let rec aux i acc =
    if i = down then acc
    else aux (i - 1) (f i acc)
  in
  aux from init
