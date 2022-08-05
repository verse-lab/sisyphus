open Common

let list_partition p lst =
  let rec loop yesdst nodst = function
    | [] -> ()
    | h :: t ->
      if p h then
        loop (accum yesdst h) nodst t
      else
        loop yesdst (accum nodst h) t
  in
  let yesdummy = dummy () in
  let nodummy = dummy () in
  loop yesdummy nodummy lst;
  (yesdummy.tl, nodummy.tl)
