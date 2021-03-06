#!/bin/bash

# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

bold=$(tput bold)
normal=$(tput sgr0)

exit_code=0

function fancy_diff () {
    local f1="${1}"
    local f2="${2}"

    diff --color=always -u "${f1}" "${f2}"
}

function run_test () {
    local has_failed=0
    local test="$1"
    local input="${test%.v}.input"
    local golden_output="${test%.v}.output"

    local output="$(mktemp)"

    echo -ne "  ${test}..."

    if [ -f "${input}" ]; then
        cat ${input} | coqc -init-file build.v ${test} 2>&1 > ${output}
    else
        coqc -init-file build.v ${test} 2>&1 > ${output}
    fi

    # we first check whether or not `coqc' was happy with our test
    if [ $? -ne 0 ]; then
        has_failed=1
        exit_code=1
    fi

    # then, we check the output produced by the command if necessary
    if [ -f "${golden_output}" ]; then
        local diff=$(fancy_diff "${golden_output}" "${output}")

        if [[ ! -z ${diff} ]]; then
            echo -e "\r                                                                        "
            echo "${bold}Output differed from expected:${normal}"
            echo "${diff}"
            echo ""

            has_failed=1
            exit_code=1
        fi

    fi

    # turns out everything went fine
    if [[ ${has_failed} -eq 0 ]]; then
        echo -e "\r  ${test}... \e[32mpass\e[39m"
    else
        echo -e "\r  ${test}... \e[31mfail\e[39m"
        echo ""
        echo "${bold}Output was:${normal}"
        cat "${output}"
        echo ""

    fi

    rm ${output}
}

for test in tests/*.v; do
    run_test ${test}
done

exit ${exit_code=}
