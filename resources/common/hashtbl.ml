
type 'a hashtbl = {
  mutable size: int;
  mutable elements: (int * 'a) list
}

let create () : 'a hashtbl  = {size=0; elements=[]}

let remove (tbl: 'a hashtbl) (key: int) =
  let rec loop ls =
    match ls with
    | [] -> []
    | h :: t ->
      if (fst h) = key
      then (tbl.size <- tbl.size - 1; loop t)
      else h :: loop t in
  let elts = loop tbl.elements in
  tbl.elements <- elts
 
let add (tbl: 'a hashtbl) (k: int) (v: 'a) =
  remove tbl k;
  tbl.elements <- (k,v) :: tbl.elements;
  tbl.size <- tbl.size + 1

let fold (tbl: 'a hashtbl) (f: 'c -> (int * 'a) -> 'c) (init: 'c) =
  let rec loop acc ls =
    match ls with
    | [] -> []
    | h :: t ->
      let acc = f acc h in
      loop acc t in
  let res = loop init tbl.elements in
  res

let iter (tbl: 'a hashtbl) (f: (int * 'a) -> unit) =
  let rec loop ls =
    match ls with
    | [] -> ()
    | h :: t ->
      f h;
      loop t in
  let res = loop tbl.elements in
  res
