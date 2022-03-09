open Containers

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)


module Heaplet = struct

  type t = PointsTo of string * Expr.t
  [@@deriving show, eq, ord]

  let pp (fmt: Format.formatter) (PointsTo (vl, expr)) =
    Format.fprintf fmt "%s ~> %a"  vl Expr.pp expr

  let subst map =
    function PointsTo (v, body) ->
      let v = match (map v: 'a Expr.shape option) with
          None -> v | Some (`Var v) -> v in
      let body = Expr.subst map body in
      PointsTo (v, body)
  [@@warning "-8"]

  let subst_var map =
    function PointsTo (v, body) ->
      let v = match map v with None -> v | Some v -> v in
      let body = Expr.subst_var map body in
      PointsTo (v, body)

  let vars ?with_funs map = function PointsTo (v, body) ->
    map
    |> StringSet.add v
    |> Fun.flip (Expr.vars ?with_funs) body
    
end

module ExprSet = Set.Make (Expr)
module HeapSet = Set.Make (Heaplet)

module Heap = struct
  type t = Expr.t StringMap.t
  [@@deriving eq, ord]

  let emp = StringMap.empty
  let empty = emp

  let is_empty = StringMap.is_empty

  let add_heaplet (Heaplet.PointsTo (ptr,body)) heap =
    StringMap.add ptr body heap
  let add_heaplets ls t = List.fold_left (Fun.flip add_heaplet) t ls
  let add_heaplets_iter ls t = Iter.fold (Fun.flip add_heaplet) t ls

  let filter f = StringMap.filter (fun ptr vl -> f (Heaplet.PointsTo (ptr,vl)))

  let get var heap = StringMap.find var heap

  let get_opt var heap = StringMap.find_opt var heap

  let remove var heap = StringMap.remove var heap
  let remove_heaplet (Heaplet.PointsTo (ptr,_)) heap =
    StringMap.remove ptr heap

  let iter s =
    StringMap.to_iter s
    |> Iter.map (fun (ptr,body) -> Heaplet.PointsTo (ptr,body))

  let to_list s = iter s |> List.of_iter

  let of_list ls = emp |> add_heaplets ls
  let of_iter it = emp |> add_heaplets_iter it

  let fold f init heap = iter heap |> Iter.fold f init

  let subst map (heap: t) =
    iter heap
    |> Iter.map (Heaplet.subst map)
    |> of_iter

  let subst_var map (heap: t) =
    iter heap
    |> Iter.map (Heaplet.subst_var map)
    |> of_iter

  let vars ?with_funs map heap =
    iter heap
    |> Iter.fold (Heaplet.vars ?with_funs) map

  let union h1 h2 = fold (Fun.flip add_heaplet) h1 h2

  let diff h1 h2 = fold (Fun.flip remove_heaplet) h1 h2

  let mem (Heaplet.PointsTo (ptr,body)) map =
    StringMap.find_opt ptr map
    |> Option.exists (Expr.equal body)

  let pp fmt vl =
    if is_empty vl
    then Format.fprintf fmt "emp"
    else
      Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " * ")
        Heaplet.pp fmt (to_list vl)

  let show = Format.to_string pp

end


module Assertion = struct
  type t = {phi: ExprSet.t; sigma: Heap.t} [@@deriving eq, ord]
  let pp fmt {phi; sigma} =
    let open Format in
    pp_print_string fmt "{";
    pp_open_hovbox fmt 1;
    ExprSet.pp
      ~pp_start:(fun fmt () -> pp_open_hbox fmt ())
      ~pp_sep:(fun fmt () -> pp_print_string fmt " /\\"; pp_print_space fmt ())
      ~pp_stop:(fun fmt () -> pp_close_box fmt ())
      Expr.pp fmt phi;
    pp_print_string fmt ";";
    pp_print_space fmt ();

    Heap.pp fmt sigma;

    pp_close_box fmt ();
    pp_print_string fmt "}"
  let show = Format.to_string pp

  let filter_phi pred t = {t with phi = ExprSet.filter pred t.phi}
  let filter_sigma pred t = {t with sigma = Heap.filter pred t.sigma}

  let mem_expr expr asn = ExprSet.mem expr asn.phi
  let mem_heaplet heaplet asn = Heap.mem heaplet asn.sigma

  let add_expr expr asn =
    {asn with phi = ExprSet.add expr asn.phi}
  let remove_expr expr asn = {asn with phi = ExprSet.remove expr asn.phi}
  let add_heaplet heaplet asn =
    {asn with sigma = Heap.add_heaplet heaplet asn.sigma}
  let remove_heaplet heaplet asn =
    {asn with sigma = Heap.remove_heaplet heaplet asn.sigma}

  let with_exprs : Expr.t list -> t -> t =
    fun exprs t ->  {t with phi=ExprSet.add_list t.phi exprs }
  let with_exprs_iter : Expr.t Iter.t -> t -> t =
    fun exprs t ->  {t with phi=ExprSet.add_iter t.phi exprs }
  let with_heaplets : Heaplet.t list -> t -> t =
    fun heaplets t -> {t with sigma=Heap.add_heaplets heaplets t.sigma}
  let with_heaplets_iter : Heaplet.t Iter.t -> t -> t =
    fun heaplets t -> {t with sigma=Heap.add_heaplets_iter heaplets t.sigma}

  let empty =  {phi=ExprSet.empty; sigma=Heap.empty}    

  let diff {phi=phi1;sigma=sigma1} {phi=phi2;sigma=sigma2} =
    {phi=ExprSet.diff phi1 phi2; sigma=Heap.(diff sigma1 sigma2)}

  let vars ?with_funs asn map =
    Heap.vars ?with_funs (ExprSet.fold (Fun.flip (Expr.vars ?with_funs))
                            asn.phi map)
      asn.sigma

  let subst map asn =
    {phi = ExprSet.map (Expr.subst map) asn.phi; sigma= Heap.subst map asn.sigma}

  let subst_var map asn =
    {phi = ExprSet.map (Expr.subst_var map) asn.phi; sigma= Heap.subst_var map asn.sigma}

  let map_heap f asn = {asn with sigma= f asn.sigma}

end
