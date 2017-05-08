#!/bin/bash

PATH_TO_CONFIGS="examples/CAV-experiments"
PATH_TO_LOGS="$PATH_TO_CONFIGS/results"
SYNET_SCRIPT="synet.py"

TOPOLOGY=$1
MODE=$2
NETS=$3
RUN_ID=$4

LOG_FILE="$PATH_TO_LOGS/$TOPOLOGY-$MODE-$NETS-$RUN_ID.txt"

echo "Running $TOPOLOGY $MODE $NETS $RUN_ID"

START=$(date +%s)
python $SYNET_SCRIPT -i $PATH_TO_CONFIGS/$TOPOLOGY-$MODE-$NETS.logic -r $PATH_TO_CONFIGS/$TOPOLOGY-$MODE-$NETS-req.logic -u 1 -m $MODE > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Synthesis time: $TIME" >> $LOG_FILE
