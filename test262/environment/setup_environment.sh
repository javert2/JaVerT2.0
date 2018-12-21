#!/bin/bash
mkdir -p environment
cp -r src/Examples environment

cp scripts/*.sh environment
cp *.native environment

cp src/JSLogic/runtime/* environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/biruntime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JS2JSIL/ES5_runtime/*.jsil environment

# test262 tests
rm -rf test262/environment
cp -r environment test262/environment