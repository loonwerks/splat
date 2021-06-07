#!/usr/bin/env bash
#
set -e

export SCRIPT_HOME=$( cd "$( dirname "$0" )" &> /dev/null && pwd )
cd $SCRIPT_HOME
export BASE_NAME=mon2.opt.hamr
~/bin/cake-x64-32/cake --target=arm7 --heap_size=4 --stack_size=4 < ${SCRIPT_HOME}/${BASE_NAME}.cml > ${SCRIPT_HOME}/${BASE_NAME}.S
sed -i 's/cdecl(main)/cdecl(run)/' ${SCRIPT_HOME}/${BASE_NAME}.S

