#!/bin/bash

PATH_TO_CONFIGS="examples/CAV-experiments"
PATH_TO_LOGS="$PATH_TO_CONFIGS/results"
SYNET_SCRIPT="synet.py"

TOPOLOGY=$1
MODE=$2
RUN_ID=$3

LOG_FILE="$PATH_TO_LOGS/$TOPOLOGY-$MODE-$RUN_ID.txt"

echo "$TOPOLOGY $MODE $RUN_ID"

START=$(date +%s)
python $SYNET_SCRIPT -i $PATH_TO_CONFIGS/$TOPOLOGY-$MODE.logic -r $PATH_TO_CONFIGS/$TOPOLOGY-$MODE-req.logic -u 1 -m $MODE > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Synthesis time: $TIME" >> $LOG_FILE
