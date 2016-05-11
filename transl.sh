#!/bin/bash

file=$1

./bin/release/mm  -i ${file}.mm  -o $file.smm
./bin/release/smm -i ${file}.smm -o ${file}.rus
./bin/release/mdl -i ${file}.rus -o ${file}.smm
./bin/release/smm -i ${file}.smm