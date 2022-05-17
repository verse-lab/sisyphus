module Symbol = Sisyphus_tracing.Symbol

type value = [%import: Sisyphus_tracing.value]
[@@deriving show, eq]

type heaplet = [%import: Sisyphus_tracing.heaplet]
[@@deriving show, eq]
