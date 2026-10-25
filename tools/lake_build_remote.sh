#!/usr/bin/env bash
# Mac → lean-node 的乾淨 lake build，一支跑完：推送工作樹（不含 evidence/、.git）到節點的全新目錄
# → 等節點空下來（真正的 lean 程序 < 2，最多等 1 小時）→ 跑 tools/lake_build_node.sh → 收回證據到
# evidence/er_epr_<UTC>_lakebuild/ → 清掉節點上的工作目錄。原始碼只單向 Mac → 節點；節點上不做 git。
# 用法：tools/lake_build_remote.sh
set -euo pipefail
REPO=/Users/liweiting/Documents/alloy/er_epr_lean
NODE_ENV=/Users/liweiting/Documents/alloy/infra/remote_node/bin/node.env.lean-node
[ -f "$NODE_ENV" ] || { echo "missing $NODE_ENV" >&2; exit 2; }
read -r NODE_HOST NODE_USER NODE_PORT < <(
  set +u
  # shellcheck source=/dev/null
  source "$NODE_ENV" >/dev/null
  printf '%s %s %s\n' "${NODE_HOST:-}" "${NODE_USER:-}" "${NODE_PORT:-}"
)
: "${NODE_HOST:?}" "${NODE_USER:?}" "${NODE_PORT:?}"
HOST="$NODE_USER@$NODE_HOST"
OPTS=(-o BatchMode=yes -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ServerAliveInterval=30 -o Port="$NODE_PORT")

UTC=$(date -u +%Y%m%dT%H%M%SZ)
W="/home/lean/alloy_node/lakebuild/er_epr_${UTC}"
S="${W%/*}/run_${W##*/}.sh"
cd "$REPO"
ssh "${OPTS[@]}" "$HOST" "mkdir -p $W"
tar -c --exclude=./evidence --exclude=./.git . 2>/dev/null | ssh "${OPTS[@]}" "$HOST" "tar -x -C $W 2>/dev/null"
scp -q "${OPTS[@]}" tools/lake_build_node.sh "$HOST:$S"
echo "pushed $W"

ssh "${OPTS[@]}" "$HOST" "t=0; while [ \$(pgrep -xc lean || true) -ge 2 ] && [ \$t -lt 3600 ]; do sleep 30; t=\$((t+30)); done; echo waited=\$t; nohup bash $S $W > $W.nohup.log 2>&1 < /dev/null & while [ ! -f $W/DONE ]; do sleep 20; done; echo done"

L="$REPO/evidence/er_epr_${UTC}_lakebuild"
mkdir -p "$L"
# scp（SFTP 模式）不展開遠端的大括號與萬用字元，改用 ssh＋tar 收回
ssh "${OPTS[@]}" "$HOST" "cd $W && tar -c receipt.txt axioms.out coupling.out built_oleans.txt package_heads.txt lake_du.txt lake_build*.log time_*.log cache_get.log 2>/dev/null" \
  | tar -x -C "$L"
touch "$L/DONE"
# 證據收回後清掉節點上的工作目錄（每次約 7.7 GB 的 mathlib 編譯產物，可隨時重建）。
# 2026-10-24 累積 20 個把節點磁碟塞滿，之後一律收完就清；只清本次建立的三個路徑。
case "$W" in
  /home/lean/alloy_node/lakebuild/er_epr_*) ssh "${OPTS[@]}" "$HOST" "rm -rf -- '$W' '$S' '$W.nohup.log'" ;;
  *) echo "refuse to clean unexpected path: $W" >&2 ;;
esac
echo "evidence: $L"
/usr/bin/grep -v '^sha256 ' "$L/receipt.txt"
