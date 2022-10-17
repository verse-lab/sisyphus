type 'a t = {
  mutable size: int;
  mutable vec: 'a array
}

let array_fill arr start len vl =
  let stop = start + len in
  let rec loop start =
    if start < stop
    then (arr.(start) <- vl; loop (start + 1))
    else () in
  loop start


let vec_size (v: 'a t) = v.size

let vec_get (v: 'a t) (i: int) = v.vec.(i)

let vec_set (v: 'a t) (i: int) (vl: 'a) = v.vec.(i) <- vl

let vec_fill (v: 'a t) (start: int) (len: int) (vl: 'a) = array_fill v.vec start len vl

let vec_set_size (v: 'a t) (i: int) = v.size <- i
