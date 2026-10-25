#!/usr/bin/env bash
# lean-node 探針：依序編 ErEpr/ 下各模組（MODS 順序），再編根檔 ErEpr.lean。
# 借 chemical_quantum 現成 mathlib；olean 只寫在本證據目錄的 build/，不碰 $NODE_SRC。
# 用法：run_probe.sh <證據目錄>（目錄內已有 ErEpr/*.lean）
set -u
D="$1"
PROJ="$HOME/alloy_node/src/chemical_quantum"
MODS=(Basic NoSignalling TFD MPS Entropy NoGo Klein ER Hawking TensorNetwork Chain KMS KMSPair Charts MinCut Triangle Modular FirstLaw FirstLawGeneral GammaRotation Unruh Landauer Correlated Measurement Monogamy Swapping Coupling Axioms)

# 守門：同時最多 7 條 Lean（政策 2026-09-23-v2）、MemAvailable ≥ 12 GiB
# 只數真正的 lean 程序（-x 比對程序名）；外層的 /usr/bin/time、nice 包裝不算
NLEAN=$(pgrep -xc lean || true)
if [ "$NLEAN" -ge 7 ]; then echo "REFUSE: $NLEAN lean processes running" | tee "$D/receipt.txt"; touch "$D/DONE"; exit 3; fi
AVAIL_KB=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
if [ "$AVAIL_KB" -lt $((12*1024*1024)) ]; then echo "REFUSE: MemAvailable ${AVAIL_KB} kB < 12 GiB" | tee "$D/receipt.txt"; touch "$D/DONE"; exit 3; fi

TC="$(cat "$PROJ/lean-toolchain")"
LEAN="$HOME/.elan/toolchains/$(echo "$TC" | sed 's#/#--#; s#:#---#')/bin/lean"
cd "$D" || exit 2
mkdir -p build/ErEpr
{
  echo "host=$(hostname) utc=$(date -u +%Y%m%dT%H%M%SZ)"
  echo "uname=$(uname -srm) nproc=$(nproc)"
  echo "toolchain=$TC"
  echo "lean_version=$("$LEAN" --version)"
  echo "mathlib_rev=$(python3 -c 'import json,sys;print([p["rev"] for p in json.load(open(sys.argv[1]))["packages"] if p["name"]=="mathlib"][0])' "$PROJ/lake-manifest.json" 2>&1)"
  for m in "${MODS[@]}"; do echo "sha256_$m=$(sha256sum "ErEpr/$m.lean" | cut -d' ' -f1)"; done
  echo "lean_procs_before=$NLEAN memavail_kb=$AVAIL_KB"
} > receipt.txt

LP="$D/build"
for p in "$PROJ"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$p"; done
export LEAN_PATH="$LP"
export MIMALLOC_ALLOW_LARGE_OS_PAGES=0 MIMALLOC_PURGE_DELAY=0

RC_ALL=0
for m in "${MODS[@]}"; do
  CMD=("$LEAN" -M 8192 -j 1 -DwarningAsError=true
       -o "build/ErEpr/$m.olean" -i "build/ErEpr/$m.ilean" "ErEpr/$m.lean")
  echo "actual_cmdline_$m=nice -n 19 prlimit --core=0:0 ${CMD[*]}" >> receipt.txt
  /usr/bin/time -v -o "time_$m.log" nice -n 19 prlimit --core=0:0 "${CMD[@]}" > "lean_$m.out" 2>&1
  RC=$?
  echo "rc_$m=$RC" >> receipt.txt
  if [ "$RC" -ne 0 ]; then RC_ALL=$RC; break; fi
done
# 根檔 ErEpr.lean（lakefile 的 lean_lib 根），只 import 各模組
if [ "$RC_ALL" -eq 0 ] && [ -f ErEpr.lean ]; then
  CMD=("$LEAN" -M 8192 -j 1 -DwarningAsError=true -o build/ErEpr.olean -i build/ErEpr.ilean ErEpr.lean)
  echo "sha256_root=$(sha256sum ErEpr.lean | cut -d' ' -f1)" >> receipt.txt
  echo "actual_cmdline_root=nice -n 19 prlimit --core=0:0 ${CMD[*]}" >> receipt.txt
  nice -n 19 prlimit --core=0:0 "${CMD[@]}" > lean_root.out 2>&1
  RC=$?; echo "rc_root=$RC" >> receipt.txt
  [ "$RC" -ne 0 ] && RC_ALL=$RC
fi
echo "rc=$RC_ALL" >> receipt.txt
touch DONE
