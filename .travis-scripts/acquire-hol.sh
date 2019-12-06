#!/bin/bash

set -e

HOL_BASE="https://github.com/HOL-Theorem-Prover/HOL.git"


# Defaults:
HOL_CHECKOUT=${HOL_CHECKOUT:-master}
SML=${SML:-poly}

git clone -b $HOL_CHECKOUT $HOL_BASE
pushd HOL
eval `opam config env` && $SML < tools/smart-configure.sml && bin/build $BUILDOPTS --nograph
popd
