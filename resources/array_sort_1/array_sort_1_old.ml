open Common

let sort arr ~compare ~left ~right =
   let insert pos v =
     let rec loop i =
       let i_next = i - 1 in
       if i_next >= left && compare (Array.get arr i_next) v > 0 then begin
         Array.set arr i (Array.get arr i_next);
         loop i_next
       end
       else i in
     let final_pos = loop pos in
     Array.set arr final_pos v
   in
   for i = left + 1 to right do
     insert i (Array.get arr i)
   done