#!/bin/bash

# first, work out the paths we are referring to relative to the root directory
ROOT=$(pwd | sed 's/\/_build\/default.*//')
FILE=$(pwd | sed 's/_build\/default\///g')
COMMON="$ROOT/resources/common"

if ! [ -d "$FILE" ]; then
    CWD="$(pwd)"
    printf "ERR: $FILE does not exist or was not a directory\n\n"
    exit 255
fi
if ! [ -d "$COMMON" ]; then
    printf "ERR: $COMMON does not exist or was not a directory\n\n"
    exit 255
fi

V_FILES=$(ls "$FILE" | grep ".*\.v$")
ML_FILES=$(ls "$FILE" | grep ".*\.ml$")

COMMON_V_FILES=$(ls "$COMMON" | grep ".*\.v$")
COMMON_MLI_FILES=$(ls "$COMMON" | grep ".*\.mli$")

COMMON_ML_DEPS=$(echo "$COMMON_MLI_FILES" | sed 's/.mli/.ml/'  | sed 's/.*/..\/common\/&/')
COMMON_V_DEPS=$(echo "$COMMON_MLI_FILES" | sed 's/.mli/_ml.v/' | sed 's/\([[:alpha:]]\)/\U\1/' | sed 's/.*/..\/common\/&/')
COMMON_VO_DEPS=$(echo "$COMMON_MLI_FILES" | sed 's/.mli/_ml.vo/' | sed 's/\([[:alpha:]]\)/\U\1/' | sed 's/.*/..\/common\/&/')
COMMON_V_VO_DEPS=$(echo "$COMMON_V_FILES" | sed 's/.v/.vo/'  | sed 's/.*/..\/common\/&/')

printf "
(rule
 (target Dummy.v)
 (deps $COMMON_VO_DEPS $COMMON_V_VO_DEPS)
 (action (run touch Dummy.v)))


"

for ML_FILE in $ML_FILES; do
    ML_BASENAME="${ML_FILE%.ml}"
    CLEANED_FILE="$ML_BASENAME.sisyphus.ml"
    V_FILE="${ML_BASENAME^}_ml.v"
    printf "
(rule
     (target $CLEANED_FILE)
     (deps $ML_FILE)
     (action (with-stdout-to $CLEANED_FILE
          (run sed -E \"s/\\\\\\[@.*\\\\\\]//\" $ML_FILE))))

(rule
 (target $V_FILE)
 (deps $CLEANED_FILE $COMMON_V_DEPS $COMMON_ML_DEPS)
 (action (run cfmlc -I ../common -o ./$V_FILE $CLEANED_FILE)))
"
done
