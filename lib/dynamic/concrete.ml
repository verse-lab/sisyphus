module IntMap = Map.Make(Int)

type value = [
  | `Int of int
  | `Bool of bool
  | `Value of string
  | `List of value list
  | `Tuple of value list
  | `Constructor of string * value list
] [@@deriving show]

type heaplet = [
    `PointsTo of value
  | `Array of value list
]  [@@deriving show]

let rec sanitise_value : Sisyphus_tracing.value -> value = function
  | `Tuple vls ->  `Tuple (List.map sanitise_value vls)
  | `List vls -> `List (List.map sanitise_value vls)
  | `Int n -> `Int n
  | `Bool b -> `Bool b
  | `Value s -> `Value (Sisyphus_tracing.Symbol.show s)
  | `Constructor (name, vls) -> `Constructor (name, List.map sanitise_value vls)

let sanitise_heaplet : Sisyphus_tracing.heaplet -> heaplet = function
  | `PointsTo vl -> `PointsTo (sanitise_value vl)
  | `Array vls -> `Array (List.map sanitise_value vls)

type context = (string * value) list
type heap_context = (string * heaplet) list

let sanitise_context ctx = List.map (fun (name, vl) -> (name, sanitise_value vl)) ctx
let sanitise_heap_context ctx = List.map (fun (name, vl) -> (name, sanitise_heaplet vl)) ctx

type t = Parsetree.expression list * (context * heap_context) list IntMap.t

let build (args: Parsetree.expression list) (trace: Sisyphus_tracing.trace) : t =
  let mapping =
  List.fold_left (fun map v ->
    IntMap.update v.Sisyphus_tracing.position
      (fun ls -> Some ((sanitise_context v.env, sanitise_heap_context v.heap) :: Option.value ~default:[] ls)) map
    ) IntMap.empty trace in
  args, mapping

let lookup (_, v) pos =
  IntMap.find_opt pos v |> Option.value ~default:[]
