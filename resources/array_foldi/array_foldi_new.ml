open Common

let foldi t ~init ~f =
  let acc = ref init in
  for i = 0 to length t - 1 do
    acc := f i !acc (Array.get t i)
  done;
  !acc
