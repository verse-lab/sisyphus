open Common

let partition p a =
  let n = length a in
  if n = 0 then ([||], [||])
  else
    let ok_count = ref 0 in
    let mask =
      Array.init n (fun i ->
          let pi = p (Array.get a i) in
          if pi then incr ok_count;
          pi) in
    let ko_count = n - !ok_count in
    let init = Array.get a 0 in
    let ok = Array.make !ok_count init in
    let ko = Array.make ko_count init in
    let j = ref 0 in
    let k = ref 0 in
    for i = 0 to n - 1 do
      let x = Array.get a i in
      let px = Array.get mask i in
      if px then
        (Array.set ok !j x;
         incr j)
      else
        (Array.set ko !k x;
         incr k)
    done;
    (ok, ko)