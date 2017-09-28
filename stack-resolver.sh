#!/usr/bin/sh

RESOLVER="${1}"
STACK_FILES="./specs/x86/x86-hs/stack.yaml ./poc/poc-hs/stack.yaml"

if [[ -z "${1}" ]]; then
    echo "usage: ${0} [RESOLVER]"
    exit 1
fi

for stack in ${STACK_FILES}; do
    echo [*] "Updating ${stack} with ${RESOLVER}"
    sed -i -e "s/resolver:.*$/resolver: ${RESOLVER}/" ${stack}
done
