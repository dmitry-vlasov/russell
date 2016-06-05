#!/bin/bash

file=$1

if [ -d tmp ] 
then
    rm -fr tmp
fi

mkdir tmp

cp ${file}.mm ./tmp/${file}.mm
cd tmp

echo "mm -> smm"
../bin/release/mm  -v -i ${file}.mm  -o $file.smm
echo -e 'done\n\n'

echo "smm -> rus"
../bin/release/smm -v -i ${file}.smm -o ${file}.rus
echo -e 'done\n\n'

echo "rus -> rus'"
../bin/release/mdl -v -g -i ${file}.rus -o ${file}-1.rus
echo -e 'done\n\n'

echo "rus' -> smm'"
../bin/release/mdl -v -i ${file}-1.rus -o ${file}-1.smm
echo -e 'done\n\n'

echo "verify smm'"
../bin/release/smm -v -i ${file}-1.smm
echo -e 'done\n'

echo "smm' -> mm'"
../bin/release/smm -v -i ${file}-1.smm -o ${file}-1.mm
echo -e 'done\n\n'

echo "verify mm'"
metamath "read ${file}-1.mm" 'verify proof *' exit
echo -e 'done\n'

echo -e 'translation tests passed =)\n'

