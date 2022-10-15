
type ('a, 'b) hashtbl = {
  mutable size: int;
  mutable elements: ('a * 'b) list
}

let create () : ('a, 'b) hashtbl  = {size=0; elements=[]}

let remove (tbl: ('a, 'b) hashtbl) key =
  let rec loop ls =
    match ls with
    | [] -> []
    | h :: t ->
      if (fst h) = key
      then (tbl.size <- tbl.size - 1; loop t)
      else h :: loop t in
  let elts = loop tbl.elements in
  tbl.elements <- elts
 
let add tbl k v =
  remove tbl k;
  tbl.elements <- (k,v) :: tbl.elements;
  tbl.size <- tbl.size + 1

let fold tbl f init =
  let rec loop acc ls =
    match ls with
    | [] -> []
    | h :: t ->
      let acc = f acc h in
      loop acc t in
  let res = loop init tbl.elements in
  res

let iter tbl f =
  let rec loop ls =
    match ls with
    | [] -> ()
    | h :: t ->
      f (fst h) (snd h);
      loop t in
  let res = loop tbl.elements in
  res
