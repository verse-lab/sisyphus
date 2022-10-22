open Containers

let seq_map_product_l (type a b) (f: a -> b Seq.t) (l: a Seq.t) : b list Seq.t =
  let rec prod_rec  (left: b list) (right: a CCSeq.t) () =
    match right () with
    | Seq.Nil -> Seq.Cons (List.rev left, Seq.nil)
    | Seq.Cons (l1, tail) ->
      let (l1: b CCSeq.t) = f l1 in
      Seq.flat_map (fun l1_elt ->
        prod_rec (l1_elt::left) tail
      ) l1 () in
  prod_rec [] l
