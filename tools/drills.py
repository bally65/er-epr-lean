#!/usr/bin/env python3
"""一鍵重跑全部反向演習（清單在 tools/drills_manifest.json）。

每份演習：把現行 ErEpr/*.lean 複製到暫存樹 → 套改動（每筆 old 必須剛好出現一次）
→ 插入 append 區塊（改壞後陳述為假的正面反例）→ tools/node_run.sh 送節點編譯 → 解析。

判定：
- BASE（expect_green）：rc = 0；
- 其他：rc ≠ 0，且 expect 裡每個宣告都在紅名單上，且 append 區塊裡沒有任何錯誤
  （反例本身必須編得過，否則「改壞後為假」就沒有被重新確認）。
紅名單 = 第一個失敗模組的錯誤行，對回所在宣告名（run_probe.sh 在第一個失敗模組就停）。

用法：/usr/bin/python3 -I tools/drills.py [--jobs 4] [--tmp 暫存目錄] [演習名 …]
輸出：evidence/drills_<UTC>/REPORT.md 與 results.json；各演習的節點證據照常在 evidence/ 底下。
"""
import argparse
import concurrent.futures as cf
import datetime as dt
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

TOOLS = pathlib.Path(__file__).resolve().parent
REPO = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from drills_extract import decl_at  # noqa: E402

TAIL = "\nend\n\nend ErEpr\n"
ERR = re.compile(r"^ErEpr/(\w+)\.lean:(\d+):\d+: error")


def build_tree(drill, root):
    tree = root / drill["name"]
    (tree / "ErEpr").mkdir(parents=True)
    for f in (REPO / "ErEpr").glob("*.lean"):
        shutil.copy2(f, tree / "ErEpr" / f.name)
    shutil.copy2(REPO / "ErEpr.lean", tree / "ErEpr.lean")
    for e in drill["edits"]:
        p = tree / e["file"]
        s = p.read_text(encoding="utf-8")
        n = s.count(e["old"])
        if n != 1:
            raise RuntimeError(f"{drill['name']}：{e['file']} 的 old 出現 {n} 次")
        p.write_text(s.replace(e["old"], e["new"]), encoding="utf-8")
    ranges = []  # (模組, 起行, 迄行)：append 區塊所在行
    for a in drill.get("append", []):
        p = tree / a["file"]
        s = p.read_text(encoding="utf-8")
        i = s.rfind(TAIL)
        if i < 0:
            raise RuntimeError(f"{drill['name']}：{a['file']} 找不到檔尾")
        s = s[:i + 1] + a["text"] + s[i + 1:]
        p.write_text(s, encoding="utf-8")
    for a in drill.get("append", []):
        p = tree / a["file"]
        s = p.read_text(encoding="utf-8")
        j = s.find(a["text"])
        lo = s[:j].count("\n") + 1
        ranges.append((pathlib.Path(a["file"]).stem, lo, lo + a["text"].count("\n") - 1))
    return tree, ranges


def run_node(name, tree, log):
    for attempt in range(10):
        r = subprocess.run([str(TOOLS / "node_run.sh"), f"rd_{name}", str(tree)],
                           capture_output=True, text=True)
        log.write_text(r.stdout + r.stderr, encoding="utf-8")
        m = re.search(r"^evidence: (.+)$", r.stdout, re.M)
        if not m:
            raise RuntimeError(f"{name}：node_run 沒回證據目錄（見 {log}）")
        ev = pathlib.Path(m.group(1))
        rec = (ev / "receipt.txt").read_text(encoding="utf-8")
        if not rec.startswith("REFUSE"):
            return ev, rec
        time.sleep(60 + 30 * attempt)
    raise RuntimeError(f"{name}：節點連續拒跑（lean 線數或記憶體守門）")


def judge(drill, tree, ranges, ev, rec):
    rcs = dict(re.findall(r"^rc_(\w+)=(\d+)$", rec, re.M))
    rc = int(re.search(r"^rc=(\d+)$", rec, re.M).group(1)) if re.search(r"^rc=", rec, re.M) else -1
    failed = [m for m, v in rcs.items() if v != "0"]
    red, in_append = [], []
    for mod in failed:
        out = ev / f"lean_{mod}.out"
        lines = (tree / "ErEpr" / f"{mod}.lean").read_text(encoding="utf-8").splitlines()
        for ln in out.read_text(encoding="utf-8", errors="replace").splitlines():
            m = ERR.match(ln)
            if not m or m.group(1) != mod:
                continue
            k = int(m.group(2))
            d = decl_at(lines, k)
            if d not in red:
                red.append(d)
            for (am, lo, hi) in ranges:
                if am == mod and lo <= k <= hi and d not in in_append:
                    in_append.append(d)

    def hit(x):
        return any(r == x or r.split(".")[-1] == x.split(".")[-1] for r in red)

    missing = [x for x in drill["expect"] if not hit(x)]
    if drill.get("expect_green"):
        ok = rc == 0
    else:
        ok = rc != 0 and not missing and not in_append
    return {"name": drill["name"], "ok": ok, "rc": rc, "failed_modules": failed, "red": red,
            "missing_expect": missing, "append_red": in_append, "evidence": ev.name,
            "done": (ev / "DONE").exists()}


def one(drill, tree, ranges, outdir):
    ev, rec = run_node(drill["name"], tree, outdir / f"log_{drill['name']}.txt")
    return judge(drill, tree, ranges, ev, rec)


def snapshot_sha():
    """開跑當下現行原始碼的 sha256（所有樹都從這一份複製）。"""
    h = hashlib.sha256()
    for f in sorted([REPO / "ErEpr.lean", *(REPO / "ErEpr").glob("*.lean")]):
        h.update(f.relative_to(REPO).as_posix().encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()


def summary(drill):
    if drill.get("expect_green"):
        return "（不改）"
    parts = []
    for e in drill["edits"]:
        o = e["old"].strip().splitlines()
        n = e["new"].strip().splitlines()
        o1 = o[0][:60] if o else "∅"
        n1 = n[-1][:60] if n else "∅（刪除）"
        parts.append(f"`{pathlib.Path(e['file']).stem}`: `{o1}` → `{n1}`")
    if drill.get("append"):
        parts.append(f"＋{len(drill['append'])} 個反例區塊")
    return "<br>".join(parts).replace("|", "\\|")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--tmp", default=None)
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    manifest = json.loads((TOOLS / "drills_manifest.json").read_text(encoding="utf-8"))
    if a.names:
        manifest = [d for d in manifest if d["name"] in a.names]
    utc = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    outdir = REPO / "evidence" / f"drills_{utc}"
    outdir.mkdir(parents=True)
    root = pathlib.Path(tempfile.mkdtemp(prefix=f"drills_{utc}_", dir=a.tmp))
    # 先一次建好全部樹：跑的過程中 repo 若被改，也不會混進後面的演習
    snap = snapshot_sha()
    trees = {d["name"]: build_tree(d, root) for d in manifest}
    if snapshot_sha() != snap:
        sys.exit("建樹途中原始碼被改了，重跑")
    results = {}
    with cf.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        futs = {ex.submit(one, d, *trees[d["name"]], outdir): d["name"] for d in manifest}
        for f in cf.as_completed(futs):
            n = futs[f]
            try:
                results[n] = f.result()
            except Exception as e:  # noqa: BLE001
                results[n] = {"name": n, "ok": False, "error": str(e)}
            r = results[n]
            print(f"{n}: {'PASS' if r['ok'] else 'FAIL'} {r.get('error', '')}", flush=True)
    order = [d["name"] for d in manifest]
    res = [results[n] for n in order]
    (outdir / "results.json").write_text(json.dumps(res, ensure_ascii=False, indent=1) + "\n",
                                         encoding="utf-8")
    npass = sum(r["ok"] for r in res)
    rows = []
    for d, r in zip(manifest, res):
        if "error" in r:
            rows.append(f"| {d['name']} | {summary(d)} | 錯誤 | {r['error']} | | |")
            continue
        expect = "、".join(f"`{x}`" for x in d["expect"]) or "全綠"
        red = "、".join(f"`{x}`" for x in r["red"][:6]) + ("…" if len(r["red"]) > 6 else "")
        verdict = "✅" if r["ok"] else "❌"
        extra = []
        if r["missing_expect"]:
            extra.append("缺：" + "、".join(r["missing_expect"]))
        if r["append_red"]:
            extra.append("反例紅：" + "、".join(r["append_red"]))
        rows.append(f"| {d['name']} | {summary(d)} | {verdict} rc={r['rc']} "
                    f"{'/'.join(r['failed_modules'])} | {expect} | {red} {'；'.join(extra)} | "
                    f"`{r['evidence']}` |")
    rep = [
        f"# 反向演習重跑報告 {utc}",
        "",
        f"清單：`tools/drills_manifest.json`（{len(manifest)} 份）。通過 {npass}/{len(res)}。",
        "",
        f"原始碼快照 sha256（`ErEpr.lean`＋`ErEpr/*.lean`，所有演習樹都從它複製）：`{snap}`",
        "",
        "判定：BASE 必須全綠；其他每份必須 rc ≠ 0、指定宣告都紅、反例區塊（若有）都綠。",
        "紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停），所以下游模組的連帶紅不在表內。",
        "",
        "| 演習 | 改動 | 結果 | 必須紅 | 實際紅（前 6） | 證據目錄 |",
        "|---|---|---|---|---|---|",
        *rows,
        "",
    ]
    (outdir / "REPORT.md").write_text("\n".join(rep), encoding="utf-8")
    print(f"{outdir}/REPORT.md  {npass}/{len(res)}")
    sys.exit(0 if npass == len(res) else 1)


if __name__ == "__main__":
    main()
