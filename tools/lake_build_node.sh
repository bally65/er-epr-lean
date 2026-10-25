#!/usr/bin/env bash
# lean-node 上的乾淨 lake build：在全新目錄裡依 lake-manifest.json 抓依賴、抓官方 mathlib 快取，
# 再 `lake build --wfail`（警告也算失敗），最後用 `lake env lean` 編公理檢查檔。
# 用法：lake_build_node.sh <工作目錄>（目錄內是 git archive 解出的 repo）
# 注意：lake 無法逐一給 lean 傳 -M，也不能限並行；為了不和節點上其他工作搶記憶體，
# 逐模組依序 `lake build <模組>`（一次一個 lean），每步前檢查 MemAvailable，最後再跑一次完整 `lake build`。
set -u
W="$1"
cd "$W" || exit 2
export PATH="$HOME/.elan/bin:$PATH"
export MIMALLOC_ALLOW_LARGE_OS_PAGES=0 MIMALLOC_PURGE_DELAY=0

# 只數真正的 lean 程序（-x 比對程序名）；外層的 /usr/bin/time、nice 包裝不算
NLEAN=$(pgrep -xc lean || true)
if [ "$NLEAN" -ge 5 ]; then echo "REFUSE: $NLEAN lean processes running" > receipt.txt; touch DONE; exit 3; fi
AVAIL_KB=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
if [ "$AVAIL_KB" -lt $((20*1024*1024)) ]; then echo "REFUSE: MemAvailable ${AVAIL_KB} kB < 20 GiB" > receipt.txt; touch DONE; exit 3; fi

{
  echo "host=$(hostname) utc=$(date -u +%Y%m%dT%H%M%SZ)"
  echo "uname=$(uname -srm) nproc=$(nproc)"
  echo "toolchain=$(cat lean-toolchain)"
  echo "lake_version=$(lake --version 2>&1)"
  echo "lean_version=$(lean --version 2>&1)"
  echo "manifest_sha256_before=$(sha256sum lake-manifest.json | cut -d' ' -f1)"
  echo "lakefile_sha256=$(sha256sum lakefile.toml | cut -d' ' -f1)"
  for f in ErEpr.lean ErEpr/*.lean; do echo "sha256 $f $(sha256sum "$f" | cut -d' ' -f1)"; done
  echo "lean_procs_before=$NLEAN memavail_kb=$AVAIL_KB"
} > receipt.txt

/usr/bin/time -v -o time_cache.log nice -n 19 prlimit --core=0:0 lake exe cache get > cache_get.log 2>&1
echo "rc_cache_get=$?" >> receipt.txt
echo "manifest_sha256_after_cache=$(sha256sum lake-manifest.json | cut -d' ' -f1)" >> receipt.txt

RC_STEPS=0
for t in ErEpr.Basic ErEpr.NoSignalling ErEpr.TFD ErEpr.MPS ErEpr.Entropy ErEpr.NoGo ErEpr.Klein ErEpr.ER ErEpr.Hawking ErEpr.TensorNetwork ErEpr.Chain ErEpr.KMS ErEpr.KMSPair ErEpr.Charts ErEpr.MinCut ErEpr.Triangle ErEpr.Modular ErEpr.FirstLaw ErEpr.FirstLawGeneral ErEpr.GammaRotation ErEpr.Unruh ErEpr.Landauer ErEpr.Correlated ErEpr.Measurement ErEpr.Monogamy ErEpr.Swapping ErEpr.Coupling ErEpr; do
  A=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
  if [ "$A" -lt $((20*1024*1024)) ]; then echo "STOP_before_$t: MemAvailable ${A} kB < 20 GiB" >> receipt.txt; RC_STEPS=9; break; fi
  /usr/bin/time -v -o "time_build_$t.log" nice -n 19 prlimit --core=0:0 lake build --wfail "$t" > "lake_build_$t.log" 2>&1
  R=$?; echo "rc_lake_build_$t=$R memavail_kb_before=$A" >> receipt.txt
  if [ "$R" -ne 0 ]; then RC_STEPS=$R; break; fi
done
echo "rc_steps=$RC_STEPS" >> receipt.txt
if [ "$RC_STEPS" -eq 0 ]; then
  /usr/bin/time -v -o time_build.log nice -n 19 prlimit --core=0:0 lake build --wfail > lake_build.log 2>&1
  echo "rc_lake_build=$?" >> receipt.txt
else
  echo "rc_lake_build=skipped" >> receipt.txt
fi
echo "manifest_sha256_after_build=$(sha256sum lake-manifest.json | cut -d' ' -f1)" >> receipt.txt

nice -n 19 prlimit --core=0:0 lake env lean -M 8192 -j 1 -DwarningAsError=true ErEpr/Axioms.lean \
  > axioms.out 2>&1
echo "rc_axioms=$?" >> receipt.txt

nice -n 19 prlimit --core=0:0 lake env lean -M 8192 -j 1 -DwarningAsError=true ErEpr/Coupling.lean \
  > coupling.out 2>&1
echo "rc_coupling=$?" >> receipt.txt

ls -l .lake/build/lib/lean/ErEpr.olean .lake/build/lib/lean/ErEpr/*.olean > built_oleans.txt 2>&1
for p in .lake/packages/*; do
  echo "$(basename "$p") $(cat "$p/.git/HEAD" 2>/dev/null)"
done > package_heads.txt
du -sh .lake > lake_du.txt 2>&1
touch DONE
