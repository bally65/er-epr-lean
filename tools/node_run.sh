#!/usr/bin/env bash
# Mac → lean-node 單行道：把 <來源目錄>/ErEpr/*.lean 推到節點新的探針目錄，
# 在節點跑 run_probe.sh，再把證據（receipt、lean 輸出、time log、原始碼）收回本機 evidence/。
# 用法：node_run.sh <標籤> [來源目錄，預設本 repo]
set -euo pipefail
LABEL="${1:?label}"
REPO=/Users/liweiting/Documents/alloy/er_epr_lean
SRC_DIR="${2:-$REPO}"
# 連線位址從 infra 的節點設定檔讀；只取 NODE_HOST／NODE_USER／NODE_PORT 三個變數，
# 在子 shell 裡 source，設定檔的其他變數不會進到本腳本。
NODE_ENV=/Users/liweiting/Documents/alloy/infra/remote_node/bin/node.env.lean-node
[ -f "$NODE_ENV" ] || { echo "missing $NODE_ENV" >&2; exit 2; }
read -r NODE_HOST NODE_USER NODE_PORT < <(
  set +u
  # shellcheck source=/dev/null
  source "$NODE_ENV" >/dev/null
  printf '%s %s %s\n' "${NODE_HOST:-}" "${NODE_USER:-}" "${NODE_PORT:-}"
)
: "${NODE_HOST:?NODE_HOST unset in $NODE_ENV}" "${NODE_USER:?NODE_USER unset}" "${NODE_PORT:?NODE_PORT unset}"
HOST="$NODE_USER@$NODE_HOST"
OPTS=(-o BatchMode=yes -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o Port="$NODE_PORT")
UTC=$(date -u +%Y%m%dT%H%M%SZ)
NAME="er_epr_${UTC}_${LABEL}"
R="/home/lean/alloy_node/probe/$NAME"

ssh "${OPTS[@]}" "$HOST" "mkdir -p $R/ErEpr"
scp -q "${OPTS[@]}" "$SRC_DIR"/ErEpr/*.lean "$HOST:$R/ErEpr/"
[ -f "$SRC_DIR/ErEpr.lean" ] && scp -q "${OPTS[@]}" "$SRC_DIR/ErEpr.lean" "$HOST:$R/"
scp -q "${OPTS[@]}" "$REPO/tools/run_probe.sh" "$HOST:$R/"
ssh "${OPTS[@]}" "$HOST" "bash $R/run_probe.sh $R" || true

L="$REPO/evidence/$NAME"
mkdir -p "$L/ErEpr"
scp -q "${OPTS[@]}" "$HOST:$R/receipt.txt" "$HOST:$R/lean_*.out" "$HOST:$R/time_*.log" "$L/" || true
scp -q "${OPTS[@]}" "$HOST:$R/ErEpr/*.lean" "$L/ErEpr/"
ssh "${OPTS[@]}" "$HOST" "test -f $R/DONE" && touch "$L/DONE"
echo "evidence: $L"
cat "$L/receipt.txt"
