#!/bin/bash

file=$1

time {
	echo "Verifying: $file.js"
	./js2jsil.native -file Examples/JaVerT/$file.js -logic -unfolds &> /dev/null
	rc=$?; if [[ $rc != 0 ]]; then echo "Failed js2jsil on $file"; fi
    if [[ $2 == "count" ]]; then
	    ./jsilverify.native -file Examples/JaVerT/$file.jsil -silent -stats $params
    else
        ./jsilverify.native -file Examples/JaVerT/$file.jsil -silent $params
    fi
}
echo "----------------"