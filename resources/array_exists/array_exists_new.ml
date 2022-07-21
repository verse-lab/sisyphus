open Common

let array_exists t ~f =
  let i = ref 0 in
  let result = ref false in
  let rec loop () =
    if !i < (length t) && not !result then begin
      if f (Array.get t !i) then result := true else decr i;
      loop ();
    end
  in
  loop ();
  !result
