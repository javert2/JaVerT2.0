#!/bin/bash

# Bash array format: ("one" "two" "three")
# JS Files to test
declare -a jsfiles=("BST" "DLL" "ExprEval" "IDGen" "KVMap" "PriQ" "SLL" "Sort" "test262/switch-01" "test262/switch-02" "test262/try-catch-01" "test262/try-catch-02" "test262/try-catch-03")

if [[ $1 == "fast" ]]; then
	params="-nochecks -nooutput"
else 
	params=""
fi

echo "Verifying JaVerT examples"
echo "-------------------------"
for f in "${jsfiles[@]}"
do
    sleep 3
	./JaVerT.sh $f $1
done
