open Containers
open Utils

type sanitized_state = {
  id: int;
  env: Runtime.value stringmap;
  heap: Runtime.heaplet stringmap;
} [@@deriving show, eq]

let sanitize_state ({position=id; env; heap}: Sisyphus_tracing.state) : sanitized_state = {
  id; env = StringMap.of_list env; heap = StringMap.of_list heap
}
let sanitize_trace ls = List.map sanitize_state ls


type scorer = sanitized_state -> sanitized_state -> float option

type t = float intpairmap    (* mapping of (loc 1,loc 2) to float scores *)

let score scorers s1 s2 =
  List.filter_map (fun f -> f s1 s2) scorers
  |> List.fold_left (+.) 0.

let value_size (vl: Runtime.value) =
  Float.of_int @@ match vl with
    | `List vl -> List.length vl
    | `Tuple vl -> List.length vl
    | `Int _ -> 1
    | `Value _ -> 5
    | `Constructor (_, vl) -> List.length vl

let heaplet_size vl =
  match vl with
    | `PointsTo _ -> 1.0
    | `Array ls -> 1.0 +. (Float.of_int (List.length ls)) /. 100.  

let _heap_size s1 =
  StringMap.fold (fun _ vl acc ->
    acc +. heaplet_size vl
  ) s1.heap 0.

let heaplet_matches (v1: Runtime.heaplet) (v2: Runtime.heaplet) =
  match v1, v2 with
  | (`PointsTo v1, `PointsTo v2) -> Runtime.equal_value v1 v2
  | (`Array v1, `Array v2) -> List.equal Runtime.equal_value v1 v2
  | (`PointsTo (`List v1), `Array v2) -> List.equal Runtime.equal_value v1 v2
  | (`Array v1, `PointsTo (`List v2)) -> List.equal Runtime.equal_value v1 v2
  | (`PointsTo v1, `Array [v2]) -> Runtime.equal_value v1 v2
  | (`Array [v1], `PointsTo v2) -> Runtime.equal_value v1 v2
  | _ -> false

let value_matches_heaplet (v1: Runtime.value) (v2: Runtime.heaplet) =
  match v1, v2 with
  | (v1, `PointsTo v2) -> Runtime.equal_value v1 v2
  | (`List v1, `Array v2) -> List.equal Runtime.equal_value v1 v2
  | (v1, `Array [v2]) -> Runtime.equal_value v1 v2
  | _ -> false


let remove_heaplet h1 ls = remove_one ~eq:heaplet_matches h1 ls
let remove_value_from_env v1 ls = remove_one ~eq:Runtime.equal_value v1 ls
let remove_value_from_heap vl ls = remove_first ~pred:(value_matches_heaplet vl) ls

let heap_match s1 s2 =
  match () with
  | _ when StringMap.is_empty s1.heap && StringMap.is_empty s2.heap -> Some 1.
  | _ ->
    StringMap.fold (fun _ heaplet (score, s2_heap) ->
      match remove_heaplet heaplet s2_heap with
      | None -> (score, s2_heap)
      | Some s2_heap -> (score +. heaplet_size heaplet, s2_heap)
    ) s1.heap (0., StringMap.values s2.heap |> Iter.to_list)
    |> fst
    |> Option.some

let env_match s1 s2 =
  StringMap.fold (fun _ vl (score, s2_env, s2_heap) ->
    match remove_value_from_env vl s2_env, remove_value_from_heap vl s2_heap with
    | None, None -> (score, s2_env, s2_heap)
    | Some s2_env, None -> (score +. value_size vl, s2_env, s2_heap)
    | _, Some s2_heap ->   (score +. value_size vl, s2_env, s2_heap)
  ) s1.env (0., StringMap.values s2.env |> Iter.to_list, StringMap.values s2.heap |> Iter.to_list)
  |> (fun (score, _, _) -> score)
  |> Option.some

let build ?(scorers=[heap_match; env_match]) trace1 trace2 : t  =
  let trace1, trace2 = sanitize_trace trace1, sanitize_trace trace2 in
  List.product (fun s1 s2 ->
    let map = s1.id, s2.id in
    map, score scorers s1 s2
  ) trace1 trace2
  |> Iter.of_list
  |> Iter.map (fun (pair, score) -> (pair, (score, 1)))
  |> IntPairMap.of_iter_with ~f:(fun _key (s1, count1) (s2, count2) ->
    (s1 +. s2, count1 + count2))
  |> IntPairMap.map (fun (score, count) -> score /. Float.of_int count)

let top_k k side (t: t) =
  let partition = match side with
      `Left -> fun ((i1,i2), v) -> (i1, [(i2,v)])
    | `Right -> fun ((i1,i2), v) -> (i2, [(i1,v)]) in
  IntPairMap.to_iter t
  |> Iter.map partition
  |> IntMap.of_iter_with ~f:(fun _ v1 v2 -> v1 @ v2)
  |> IntMap.map (List.sort (fun (pos1, v1) (pos2, v2) ->
    Pair.compare Float.compare (fun i j -> - Int.compare i j) (v2, pos2) (v1,pos1)))
  |> IntMap.map (List.take k)
