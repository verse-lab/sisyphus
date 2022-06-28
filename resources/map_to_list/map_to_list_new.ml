open Common

let to_list map =
  List.of_seq @@ StringMap.to_seq map
