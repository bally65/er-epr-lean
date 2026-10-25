#!/usr/bin/env bash
# lean-node 上對 mathlib master 驗證「複數速率 Gamma 積分」補丁（使用者 2026-10-25 同意安裝）。
# 1. 裝 master 的 toolchain；2. 在 ~/alloy_node/upstream/ 淺層 clone mathlib master；
# 3. 抓官方快取；4. 把 section.lean 接到 Gamma/Beta.lean 尾端；5. 只建 Beta 模組；
# 6. 文字風格檢查＋該模組的定理 linter；7. 產生補丁。結果寫在 $W/report/。
# 用法：node_master_check.sh <工作目錄> <section.lean 路徑>
set -u
W="$1"; SEC="$2"
export PATH="$HOME/.elan/bin:$PATH"
export MIMALLOC_ALLOW_LARGE_OS_PAGES=0 MIMALLOC_PURGE_DELAY=0
mkdir -p "$W/report"
R="$W/report/receipt.txt"
{
  echo "host=$(hostname) utc=$(date -u +%Y%m%dT%H%M%SZ)"
  echo "lean_procs_before=$(pgrep -xc lean || true) memavail_kb=$(awk '/MemAvailable/{print $2}' /proc/meminfo)"
  df -h / | tail -1
} > "$R"

cd "$W" || exit 2
if [ ! -d mathlib4 ]; then
  git clone -q --depth 1 https://github.com/leanprover-community/mathlib4.git mathlib4 > report/clone.log 2>&1
  echo "rc_clone=$?" >> "$R"
fi
cd mathlib4 || exit 2
echo "mathlib_commit=$(git rev-parse HEAD) $(git log -1 --format=%cs)" >> "$R"
TC=$(cat lean-toolchain); echo "toolchain=$TC" >> "$R"
elan toolchain install "$TC" > ../report/toolchain.log 2>&1
echo "rc_toolchain=$?" >> "$R"
echo "lean_version=$(lake env lean --version 2>&1 | head -1)" >> "$R"

nice -n 19 prlimit --core=0:0 lake exe cache get > ../report/cache_get.log 2>&1
echo "rc_cache_get=$?" >> "$R"

F=Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean
git checkout -- "$F"
printf '\n' >> "$F"
cat "$SEC" >> "$F"
git diff > ../report/gamma-complex-rate.patch
echo "patch_sha256=$(sha256sum ../report/gamma-complex-rate.patch | cut -d' ' -f1)" >> "$R"

/usr/bin/time -v -o ../report/time_build.log nice -n 19 prlimit --core=0:0 \
  lake build --wfail Mathlib.Analysis.SpecialFunctions.Gamma.Beta > ../report/build.log 2>&1
echo "rc_build=$?" >> "$R"

nice -n 19 prlimit --core=0:0 lake exe lint-style "$F" > ../report/lint_style.log 2>&1
echo "rc_lint_style=$?" >> "$R"

nice -n 19 prlimit --core=0:0 lake exe runLinter Mathlib.Analysis.SpecialFunctions.Gamma.Beta \
  > ../report/run_linter.log 2>&1
echo "rc_run_linter=$?" >> "$R"

cat > ../report/Axioms.lean <<'EOF'
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
#print axioms Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos
#print axioms Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi
#print axioms Complex.differentiableAt_integral_cpow_mul_exp_neg_mul_Ioi
EOF
nice -n 19 prlimit --core=0:0 lake env lean -M 8192 ../report/Axioms.lean > ../report/axioms.out 2>&1
echo "rc_axioms=$?" >> "$R"
echo "lean_procs_after=$(pgrep -xc lean || true)" >> "$R"
touch ../report/DONE
