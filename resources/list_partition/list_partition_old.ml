open Common

let partition p lst =
  let rec loop yesdst nodst = function
    | [] -> ()
    | h :: t ->
      let r = create h in
      if p h then
        begin
          yesdst.tl <- inj r;
          loop r nodst t
        end
      else
        begin
          nodst.tl <- inj r;
          loop yesdst r t
        end
  in
  let yesdummy = dummy ()
  and nodummy = dummy ()
  in
  loop yesdummy nodummy lst;
  yesdummy.tl, nodummy.tl
