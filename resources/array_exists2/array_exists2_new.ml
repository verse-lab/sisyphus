open Common


let array_exists2 t1 t2 ~f =
  if (length t1) = (length t2)
  then
    let i = ref (length t1 - 1) in
    let result = ref false in
    (while !i >= 0 && not !result do
       if f (Array.get t1 !i) (Array.get t2 !i) then result := true else decr i
     done;
     !result)
  else false
