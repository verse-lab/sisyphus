open Common

let rev t =
  let len = Array.length t in
  let last = len - 1 in
  let mid = len / 2 - 1 in
  Array.iteri (fun i x ->
      if i > mid then ()
      else begin
        let x = t.(i) in
        t.(i) <- t.(last-i);
        t.(last-i) <- x;
      end
    ) t;
