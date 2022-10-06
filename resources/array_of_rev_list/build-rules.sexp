
(rule
 (target Dummy.v)
 (deps ../common/Arr_ml.vo
../common/Combinators_ml.vo
../common/Lst_ml.vo
../common/Opt_ml.vo
../common/Sseq_ml.vo ../common/Tactics.vo
../common/Utils.vo
../common/Verify_arr.vo
../common/Verify_combinators.vo
../common/Verify_list.vo
../common/Verify_opt.vo
../common/Verify_sseq.vo)
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
../common/Lst_ml.v
../common/Opt_ml.v
../common/Sseq_ml.v ../common/arr.ml
../common/combinators.ml
../common/lst.ml
../common/opt.ml
../common/sseq.ml)
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
../common/Lst_ml.v
../common/Opt_ml.v
../common/Sseq_ml.v ../common/arr.ml
../common/combinators.ml
../common/lst.ml
../common/opt.ml
../common/sseq.ml)
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
../common/Lst_ml.v
../common/Opt_ml.v
../common/Sseq_ml.v ../common/arr.ml
../common/combinators.ml
../common/lst.ml
../common/opt.ml
../common/sseq.ml)
 (action (run cfmlc -I ../common -o ./Common_ml.v common.sisyphus.ml)))
