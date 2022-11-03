module T = Gen_utils

let () =
  T.add_test "array_exists"
       ~path:"../../resources/array_exists"
       ~coq_name:"ProofsArrayExists"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"


let () =
  T.add_test "array_find_mapi"
       ~path:"../../resources/find_mapi"
       ~coq_name:"ProofsFindMapi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "array_findi"
       ~path:"../../resources/array_findi"
       ~coq_name:"ProofsArrayFindi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "array_foldi"
       ~path:"../../resources/array_foldi"
       ~coq_name:"ProofsArrayFoldi"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "array_is_sorted"
       ~path:"../../resources/array_is_sorted"
       ~coq_name:"ProofsArrayIsSorted"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "array_of_rev_list"
       ~path:"../../resources/array_of_rev_list"
       ~coq_name:"ProofsArrayOfRevList"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "array_partition"
       ~path:"../../resources/array_partition"
       ~coq_name:"ProofsArrayPartition"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "make_rev_list"
       ~path:"../../resources/make_rev_list"
       ~coq_name:"ProofsMakeRevList"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "seq_to_array"
       ~path:"../../resources/seq_to_array"
       ~coq_name:"Proofs"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"


let () =
  T.add_test "sll_of_array"
       ~path:"../../resources/sll_of_array"
       ~coq_name:"ProofsSllOfArray"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "sll_partition"
       ~path:"../../resources/sll_partition"
       ~coq_name:"ProofsSllPartition"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "stack_filter"
       ~path:"../../resources/stack_filter"
       ~coq_name:"ProofsStackFilter"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "stack_reverse"
       ~path:"../../resources/stack_reverse"
       ~coq_name:"ProofsStackReverse"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let () =
  T.add_test "tree_to_array"
       ~path:"../../resources/tree_to_array"
       ~coq_name:"ProofsTreeToArray"
       ~common_path:"../../resources/common"
       ~common_coq_name:"Common"

let test_list = Gen_utils.get_test_list ()
