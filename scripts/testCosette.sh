#!/bin/bash

filename=$1
name=${filename%%.*}
jsilname=$name'.jsil'

echo $filename

time {
./js2jsil.native -file "$filename" -cosette
./cosette.native -file "$jsilname" -silent -stats
}