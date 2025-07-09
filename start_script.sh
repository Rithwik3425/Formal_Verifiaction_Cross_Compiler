#!/bin/bash

set -e

echo -e "Starting the scripts "
chmod +x verified_compiler_pipeline.sh
./verified_compiler_pipeline.sh

cd verified_compiler/examples
chmod +x run_all_techniques.sh
./run_all_techniques.sh
