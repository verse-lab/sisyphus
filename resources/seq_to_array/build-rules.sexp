
(rule
 (target Dummy.v)
 (deps ../common/Combinators_ml.vo
../common/Opt_ml.vo
../common/Sseq_ml.vo ../common/Tactics.vo
../common/Utils.vo
../common/Verify_combinators.vo
../common/Verify_list.vo
../common/Verify_opt.vo
../common/Verify_sseq.vo)
 (action (run touch Dummy.v)))



(rule
     (target seq_to_array_new.sisyphus.ml)
     (deps seq_to_array_new.ml)
     (action (with-stdout-to seq_to_array_new.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" seq_to_array_new.ml))))

(rule
 (target Seq_to_array_new_ml.v)
 (deps seq_to_array_new.sisyphus.ml ../common/Combinators_ml.v
../common/Opt_ml.v
../common/Sseq_ml.v ../common/combinators.ml
../common/opt.ml
../common/sseq.ml)
 (action (run cfmlc -I ../common -o ./Seq_to_array_new_ml.v seq_to_array_new.sisyphus.ml)))

(rule
     (target seq_to_array_old.sisyphus.ml)
     (deps seq_to_array_old.ml)
     (action (with-stdout-to seq_to_array_old.sisyphus.ml
          (run sed -E "s/\\[@.*\\]//" seq_to_array_old.ml))))

(rule
 (target Seq_to_array_old_ml.v)
 (deps seq_to_array_old.sisyphus.ml ../common/Combinators_ml.v
../common/Opt_ml.v
../common/Sseq_ml.v ../common/combinators.ml
../common/opt.ml
../common/sseq.ml)
 (action (run cfmlc -I ../common -o ./Seq_to_array_old_ml.v seq_to_array_old.sisyphus.ml)))
