#!/bin/bash

# List of DaCapo benchmarks
BENCHMARKS=(
avrora batik  h2 luindex lusearch pmd xalan
)

for bench in "${BENCHMARKS[@]}"; do
  echo "Running benchmark: $bench"

  cd ../benchmarks/dacapo || exit
  rm -rf ./out ./scratch

  java -javaagent:poa-trunk.jar -jar dacapo-9.12-MR1-bach.jar "$bench"

  cd ../../scripts || exit
  ./benchmark.sh dacapo > "${bench}_v2.txt"

  echo "$bench completed"
  echo "------------------------"
done
