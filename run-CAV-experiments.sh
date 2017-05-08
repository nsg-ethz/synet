#!/bin/bash

PATH_TO_CONFIGS="examples/CAV-experiments"
NUM_REPEATS=10
NUM_PROCESSES=10

echo "Running CAV experiments"

find $PATH_TO_CONFIGS -type f -name *req* | sort | while read line; do 
	CONFIG=$(basename $line | sed 's/-req.logic//')
	TOPOLOGY=$(echo $CONFIG | awk -F '-' '{print $1}')
	MODE=$(echo $CONFIG | awk -F '-' '{print $2}')
	for RUN_ID in $(seq 1 $NUM_REPEATS); do
		echo $TOPOLOGY $MODE $RUN_ID
	done
done | xargs -n 3 -I{} -P $NUM_PROCESSES sh -c "sh run-config.sh {}"
