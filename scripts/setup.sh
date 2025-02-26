#!/bin/bash

# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

script_dir=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )


# libCST
## Build libCST
pushd $script_dir/../lib/libCST
git remote add upstream git@github.com:Instagram/LibCST.git
git fetch --tags upstream
rm -rf ../../build/libCST 2>/dev/null
hatch run python -m build --sdist --outdir ../../build/libCST
popd

## Install libCST
pushd $script_dir/..
libcst_package=$(find build/libCST -type f)
pip install $libcst_package
popd


# CBMC
## Add missing libstdc++.so.6 softlink for cmake
pushd $CONDA_PREFIX/lib
libcstdcpp=$(find . -name 'libstdc++.so.6.*')
ln -s $(basename $libcstdcpp) libstdc++.so.6 2>/dev/null
popd

## Build CBMC
pushd $script_dir/../lib/cbmc
git submodule update --init
cmake -S . -Bbuild
cmake --build build --target cbmc --parallel
popd

## Install CBMC
cp $script_dir/../lib/cbmc/build/bin/cbmc $CONDA_PREFIX/bin/


# Z3
## Build and install Z3
pushd $script_dir/../lib/z3
git submodule update --init
mkdir build
cd build
cmake -D CMAKE_INSTALL_PREFIX=$CONDA_PREFIX -G "Unix Makefiles" ../
make --jobs
make install
popd


# Datasets
## Download FOLIO dataset
pushd $script_dir/../datasets
huggingface-cli download --repo-type dataset allenai/ZebraLogicBench-private grid_mode/test-00000-of-00001.parquet --local-dir .
huggingface-cli download --repo-type dataset yale-nlp/FOLIO folio_v2_train.jsonl folio_v2_validation.jsonl --local-dir .
popd
