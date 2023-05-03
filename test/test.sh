#!/bin/sh

rob="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/robustness.py"
test_dir_coff="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/coffee_tea/"
test_dir_voting="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/voting/"
test_dir_therac="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/therac25/"
test_dir_fixed_mutex="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/fixed_mutex/"
test_dir_abp="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/test/abp/"

unset TLA_ROBUST_MAX_NEG_EXAMPLES

test_prop() {
    tla_file="${1}.tla"
    actual_file="out/${1}_actual.txt"
    expected_file="expected/${1}.txt"
    mkdir -p out
    python3 "${rob}" --outdir out --spec "${tla_file}" > "${actual_file}"
    diff=$(diff "${actual_file}" "${expected_file}")
    rm -rf out/
    if [[ "${diff}" = "" ]]
    then
        echo "${1} pass"
    else
        echo "${1} failed with diff (actual v. expected):"
        echo "${diff}"
        exit 0
    fi
}

test_env() {
    tla_file1="${1}.tla"
    tla_file2="${2}.tla"
    actual_file="out/${1}_${2}_actual.txt"
    expected_file="expected_env/${1}_${2}.txt"
    mkdir -p out
    python3 "${rob}" --outdir out --spec "${tla_file1}" --spec2 "${tla_file2}" --env > "${actual_file}"
    diff=$(diff "${actual_file}" "${expected_file}")
    rm -rf out/
    if [[ "${diff}" = "" ]]
    then
        echo "${1}_${2} pass"
    else
        echo "${1}_${2} failed with diff (actual v. expected):"
        echo "${diff}"
        exit 0
    fi
}

test_cmp() {
    tla_file1="${1}.tla"
    tla_file2="${2}.tla"
    actual_file="out/${1}_${2}_actual.txt"
    expected_file="expected/${1}_${2}.txt"
    mkdir -p out
    python3 "${rob}" --outdir out --spec "${tla_file1}" --spec2 "${tla_file2}" --compare > "${actual_file}"
    diff=$(diff "${actual_file}" "${expected_file}")
    rm -rf out/
    if [[ "${diff}" = "" ]]
    then
        echo "${1}_${2} pass"
    else
        echo "${1}_${2} failed with diff (actual v. expected):"
        echo "${diff}"
        exit 0
    fi
}

test_suite() {
    pushd "${1}"
    for f in `ls expected 2>/dev/null`
    do
        name=$(echo "${f}" | sed 's/\.txt$//g')
        has_underscore=$(echo "${name}" | grep "_")
        if [[ "${has_underscore}" = "" ]]
        then
            test_prop "${name}"
        else
            name1=$(echo "${name}" | sed 's/_.*$//g')
            name2=$(echo "${name}" | sed 's/^.*_//g')
            test_cmp "${name1}" "${name2}"
        fi
    done
    for f in `ls expected_env 2>/dev/null`
    do
        name=$(echo "${f}" | sed 's/\.txt$//g')
        has_underscore=$(echo "${name}" | grep "_")
        if [[ "${has_underscore}" != "" ]]
        then
            name1=$(echo "${name}" | sed 's/_.*$//g')
            name2=$(echo "${name}" | sed 's/^.*_//g')
            test_env "${name1}" "${name2}"
        fi
    done
    popd
}


test_suite "${test_dir_coff}"
test_suite "${test_dir_voting}"
test_suite "${test_dir_therac}"
test_suite "${test_dir_fixed_mutex}"
test_suite "${test_dir_abp}"
