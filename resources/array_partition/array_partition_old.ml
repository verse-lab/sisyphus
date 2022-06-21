open Common

let partition p xs =
  let n = length xs in
  (* Use a bitset to store which elements will be in which final array. *)
  let bs = Array.make n false in
  for i = 0 to n-1 do
    if p xs.(i) then Array.set bs i true
  done;
  (* Allocate the final arrays and copy elements into them. *)
  let n1 = count bs in
  let n2 = n - n1 in
  let j = ref 0 in
  let xs1 = Array.init n1
              (fun _ ->
                 (* Find the next set bit in the BitSet. *)
                 while not (Array.get bs !j) do incr j done;
                 let r = xs.(!j) in
                 incr j;
                 r) in
  let j = ref 0 in
  let xs2 = Array.init n2
              (fun _ ->
                 (* Find the next clear bit in the BitSet. *)
                 while Array.get bs !j do incr j done;
                 let r = xs.(!j) in
                 incr j;
                 r) in
  xs1, xs2
