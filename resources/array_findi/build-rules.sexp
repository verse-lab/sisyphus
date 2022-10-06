
(rule
 (target Dummy.v)
 (deps ../common/Combinators_ml.vo
../common/Sseq_ml.vo ../common/Tactics.vo
../common/Utils.vo
../common/Verify_combinators.vo
../common/Verify_list.vo
../common/Verify_sseq.vo)
 (action (run touch Dummy.v)))



(rule
     (target array_findi_new.sisyphus.ml)
     (deps array_findi_new.ml)
     (action (with-stdout-to array_findi_new.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_findi_new.ml))))

(rule
 (target Array_findi_new_ml.v)
 (deps array_findi_new.sisyphus.ml ../common/Combinators_ml.v
../common/Sseq_ml.v ../common/combinators.ml
../common/sseq.ml)
 (action (run cfmlc -I ../common -o ./Array_findi_new_ml.v array_findi_new.sisyphus.ml)))

(rule
     (target array_findi_old.sisyphus.ml)
     (deps array_findi_old.ml)
     (action (with-stdout-to array_findi_old.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" array_findi_old.ml))))

(rule
 (target Array_findi_old_ml.v)
 (deps array_findi_old.sisyphus.ml ../common/Combinators_ml.v
../common/Sseq_ml.v ../common/combinators.ml
../common/sseq.ml)
 (action (run cfmlc -I ../common -o ./Array_findi_old_ml.v array_findi_old.sisyphus.ml)))
