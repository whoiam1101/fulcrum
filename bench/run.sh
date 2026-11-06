#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
cargo bench -q --bench ops --no-run
taskset -c "${BENCH_CPU:-4}" cargo bench -q --bench ops -- --warm-up-time 1 --measurement-time "${MEASURE_SECS:-2}" --output-format bencher "$@" 2>&1 \
  | grep -E '^test' | tr -d ',' \
  | awk '{ split($2, p, "/"); n = (p[1] == "latency") ? 1024 : 4096; printf "%-11s %-4s %-24s %7.3f ns/op\n", p[1], p[2], p[3] "/" p[4], $5 / n }'
