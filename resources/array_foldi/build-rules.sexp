
(rule
 (target Dummy.v)
 (deps ../common/Arr_ml.vo
../common/Combinators_ml.vo
../common/Lst_ml.vo
../common/Opt_ml.vo
../common/Sll_ml.vo
../common/Sseq_ml.vo ../common/Solver.vo
../common/Tactics.vo
../common/Utils.vo
../common/Verify_arr.vo
../common/Verify_combinators.vo
../common/Verify_list.vo
../common/Verify_opt.vo
../common/Verify_sll.vo
../common/Verify_sseq.vo
../common/Verify_vec.vo)
 (action (run touch Dummy.v)))



(rule
     (target array_foldi_new.sisyphus.ml)
     (deps array_foldi_new.ml)
     (action (with-stdout-to array_foldi_new.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_foldi_new.ml))))

(rule
 (target Array_foldi_new_ml.v)
 (deps array_foldi_new.sisyphus.ml ../common/Arr_ml.v
../common/Combinators_ml.v
../common/Lst_ml.v
../common/Opt_ml.v
../common/Sll_ml.v
../common/Sseq_ml.v ../common/arr.ml
../common/combinators.ml
../common/lst.ml
../common/opt.ml
../common/sll.ml
../common/sseq.ml ../common/arr.cmj
../common/combinators.cmj
../common/lst.cmj
../common/opt.cmj
../common/sll.cmj
../common/sseq.cmj)
 (action (run cfmlc -I ../common -o ./Array_foldi_new_ml.v array_foldi_new.sisyphus.ml)))

(rule
     (target array_foldi_old.sisyphus.ml)
     (deps array_foldi_old.ml)
     (action (with-stdout-to array_foldi_old.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_foldi_old.ml))))

(rule
 (target Array_foldi_old_ml.v)
 (deps array_foldi_old.sisyphus.ml ../common/Arr_ml.v
../common/Combinators_ml.v
../common/Lst_ml.v
../common/Opt_ml.v
../common/Sll_ml.v
../common/Sseq_ml.v ../common/arr.ml
../common/combinators.ml
../common/lst.ml
../common/opt.ml
../common/sll.ml
../common/sseq.ml ../common/arr.cmj
../common/combinators.cmj
../common/lst.cmj
../common/opt.cmj
../common/sll.cmj
../common/sseq.cmj)
 (action (run cfmlc -I ../common -o ./Array_foldi_old_ml.v array_foldi_old.sisyphus.ml)))