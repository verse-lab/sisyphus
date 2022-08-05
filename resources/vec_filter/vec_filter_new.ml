open Common

 let filter' p v =
   let i = ref 0 in (* cur element *)
   let j = ref 0 in  (* cur insertion point *)
   let n = v.size in
   while !i < n do
     if p v.vec.(! i) then (
       (* move element i at the first empty slot.
          invariant: i >= j*)
       if !i > !j then v.vec.(!j) <- v.vec.(!i);
       incr i;
       incr j
     ) else incr i
   done;
   (* free elements *)
   if !j > 0 && !j < v.size then (
     Array.fill v.vec !j (v.size - !j) v.vec.(0);
   );
   v.size <- !j
