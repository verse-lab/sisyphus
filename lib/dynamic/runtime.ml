module Symbol = Sisyphus_tracing.Symbol

type value = [%import: Sisyphus_tracing.value]
[@@deriving show]
let equal_value = Sisyphus_tracing.equal_value

type heaplet = [%import: Sisyphus_tracing.heaplet]
[@@deriving show]
let equal_heaplet = Sisyphus_tracing.equal_heaplet
