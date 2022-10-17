
(rule
 (target Dummy.v)
 (deps ../common/Arr_ml.vo
../common/Combinators_ml.vo
../common/Hashtbl_ml.vo
../common/Lst_ml.vo
../common/Opt_ml.vo
../common/Queue_ml.vo
../common/Set_ml.vo
../common/Sll_ml.vo
../common/Sseq_ml.vo
../common/Tree_ml.vo
../common/Vec_ml.vo ../common/Solver.vo
../common/Tactics.vo
../common/Utils.vo
../common/Verify_arr.vo
../common/Verify_combinators.vo
../common/Verify_hashtbl.vo
../common/Verify_list.vo
../common/Verify_opt.vo
../common/Verify_queue.vo
../common/Verify_set.vo
../common/Verify_sll.vo
../common/Verify_sseq.vo
../common/Verify_stack.vo
../common/Verify_tree.vo
../common/Verify_vec.vo)
 (action (run touch Dummy.v)))



(rule
     (target array_of_rev_list_new.sisyphus.ml)
     (deps array_of_rev_list_new.ml)
     (action (with-stdout-to array_of_rev_list_new.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_of_rev_list_new.ml))))

(rule
 (target Array_of_rev_list_new_ml.v)
 (deps array_of_rev_list_new.sisyphus.ml ../common/Arr_ml.v
../common/Combinators_ml.v
../common/Hashtbl_ml.v
../common/Lst_ml.v
../common/Opt_ml.v
../common/Queue_ml.v
../common/Set_ml.v
../common/Sll_ml.v
../common/Sseq_ml.v
../common/Tree_ml.v
../common/Vec_ml.v ../common/arr.ml
../common/combinators.ml
../common/hashtbl.ml
../common/lst.ml
../common/opt.ml
../common/queue.ml
../common/set.ml
../common/sll.ml
../common/sseq.ml
../common/tree.ml
../common/vec.ml ../common/arr.cmj
../common/combinators.cmj
../common/hashtbl.cmj
../common/lst.cmj
../common/opt.cmj
../common/queue.cmj
../common/set.cmj
../common/sll.cmj
../common/sseq.cmj
../common/tree.cmj
../common/vec.cmj)
 (action (run cfmlc -I ../common -o ./Array_of_rev_list_new_ml.v array_of_rev_list_new.sisyphus.ml)))

(rule
     (target array_of_rev_list_old.sisyphus.ml)
     (deps array_of_rev_list_old.ml)
     (action (with-stdout-to array_of_rev_list_old.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_of_rev_list_old.ml))))

(rule
 (target Array_of_rev_list_old_ml.v)
 (deps array_of_rev_list_old.sisyphus.ml ../common/Arr_ml.v
../common/Combinators_ml.v
../common/Hashtbl_ml.v
../common/Lst_ml.v
../common/Opt_ml.v
../common/Queue_ml.v
../common/Set_ml.v
../common/Sll_ml.v
../common/Sseq_ml.v
../common/Tree_ml.v
../common/Vec_ml.v ../common/arr.ml
../common/combinators.ml
../common/hashtbl.ml
../common/lst.ml
../common/opt.ml
../common/queue.ml
../common/set.ml
../common/sll.ml
../common/sseq.ml
../common/tree.ml
../common/vec.ml ../common/arr.cmj
../common/combinators.cmj
../common/hashtbl.cmj
../common/lst.cmj
../common/opt.cmj
../common/queue.cmj
../common/set.cmj
../common/sll.cmj
../common/sseq.cmj
../common/tree.cmj
../common/vec.cmj)
 (action (run cfmlc -I ../common -o ./Array_of_rev_list_old_ml.v array_of_rev_list_old.sisyphus.ml)))

(rule
     (target common.sisyphus.ml)
     (deps common.ml)
     (action (with-stdout-to common.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" common.ml))))

(rule
 (target Common_ml.v)
 (deps common.sisyphus.ml ../common/Arr_ml.v
../common/Combinators_ml.v
../common/Hashtbl_ml.v
../common/Lst_ml.v
../common/Opt_ml.v
../common/Queue_ml.v
../common/Set_ml.v
../common/Sll_ml.v
../common/Sseq_ml.v
../common/Tree_ml.v
../common/Vec_ml.v ../common/arr.ml
../common/combinators.ml
../common/hashtbl.ml
../common/lst.ml
../common/opt.ml
../common/queue.ml
../common/set.ml
../common/sll.ml
../common/sseq.ml
../common/tree.ml
../common/vec.ml ../common/arr.cmj
../common/combinators.cmj
../common/hashtbl.cmj
../common/lst.cmj
../common/opt.cmj
../common/queue.cmj
../common/set.cmj
../common/sll.cmj
../common/sseq.cmj
../common/tree.cmj
../common/vec.cmj)
 (action (run cfmlc -I ../common -o ./Common_ml.v common.sisyphus.ml)))
