#!/bin/bash

file=$1

if [ ! -d tmp ] 
then
    mkdir tmp
fi

cp ${file}.mm ./tmp/${file}.mm
cd tmp

../bin/release/mm  -v -i ${file}.mm  -o $file.smm
../bin/release/smm -v -i ${file}.smm -o ${file}.rus
../bin/release/mdl -v -i ${file}.rus -o ${file}-1.smm
../bin/release/smm -v -i ${file}-1.smm