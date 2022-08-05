open Common

let list_partition p lst =
  let rec loop  = function
    | [] -> ()
    | h :: t ->
      let r = create h in
      if p h then
        begin
          yesdst.tl <- Some r; (* yesdst: {None, Some r} \* {r ~> MList l} *)
          loop r nodst t
        end
      else
        begin
          nodst.tl <- Some r;
          loop yesdst r t
        end
  in
  let yesdummy = dummy () in
  let nodummy = dummy () in
  loop yesdummy nodummy lst;
  proj yesdummy, proj nodummy
