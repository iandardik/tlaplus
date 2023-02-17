#!/bin/sh

jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
module="$1"

if [[ "${module}" = "" ]]
then
    echo "usage: run.sh <module>"
    exit
fi

java -jar "${jar}" -deadlock -config "${module}.cfg" "${module}.tla"
#java -jar "${jar}" "${module}.tla" "${module}.cfg"

rm -rf states/
rm -f "${module}_TTrace"*
