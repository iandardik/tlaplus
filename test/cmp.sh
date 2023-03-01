#!/bin/sh

tlcian_jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
tlc_jar="/Users/idardik/bin/tla2tools.jar"
sep_dir="/Users/idardik/Documents/CMU/folseparators"
sep_file="sep.fol"
pwd=$(pwd)

module1="$1"
module2="$2"
output="$3"

if [[ "${module1}" = "" ||  "${module2}" = "" || "${output}" = "" ]]
then
    echo "usage: cmp.sh <module1> <module2> <output>"
    exit
fi


# generate err pre and err post comparison files
mkdir -p "${output}"
java -jar "${tlcian_jar}" "${output}" "${module1}.tla" "${module1}.cfg" "${module2}.tla" "${module2}.cfg"
rm -rf states/
rm -f "${module}_TTrace"*


# run sep.fol
if [[ -f "${output}/${sep_file}" ]]
then
    sep_path="${pwd}/${output}/${sep_file}"
    pushd "${sep_dir}"
    echo "non-const part of the diff rep:"
    python3 -m separators --separate --no-cvc4 --quiet "${sep_path}" | tail -1 | jq '.formula'
    popd
fi



# run comparison
pushd "${output}"

echo "running error pre"
java -jar "${tlc_jar}" -deadlock -cleanup -config Combined_ErrPre.cfg Combined_ErrPre.tla
rm -rf states/
rm -f "${module}_TTrace"*

echo ""
echo "running error post"
java -jar "${tlc_jar}" -deadlock -cleanup -config Combined_ErrPost.cfg Combined_ErrPost.tla
rm -rf states/
rm -f "${module}_TTrace"*

popd
