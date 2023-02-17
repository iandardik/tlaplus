#!/bin/sh

jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
module1="$1"
module2="$2"

if [[ "${module1}" = "" ||  "${module2}" = "" ]]
then
    echo "usage: run.sh <module1> <module2>"
    exit
fi

java -jar "${jar}" "${module1}.tla" "${module1}.cfg" "${module2}.tla" "${module2}.cfg"

rm -rf states/
rm -f "${module}_TTrace"*
