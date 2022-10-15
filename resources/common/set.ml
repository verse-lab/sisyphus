type set = int list ref

let set_mem s ls =
  let rec loop ls =
    match ls with
    | [] -> false
    | h :: t ->
      if h = s
      then true
      else loop t in
  loop !ls

let set_add s ls =
  assert (not (set_mem s ls));
  ls := s :: !ls

let set_fold (f: 'b -> int -> 'b) (init: 'b) (ls: set) =
  let rec loop acc ls =
    match ls with
    | [] -> acc
    | h :: t ->
      let acc = f acc h in
      loop acc t in
  loop init !ls

let set_iter (f: int -> unit) (ls: set) =
  let rec loop ls =
    match ls with
    | h :: t -> f h; loop t
    | [] -> () in
  loop !ls
