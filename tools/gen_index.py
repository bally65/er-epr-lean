#!/usr/bin/env python3
"""產生 docs/THEOREM_INDEX.md：每條定理的位置、公理狀態、哪些演習打到它、哪些耦合斷言提到它。

資料來源（都是磁碟上的檔，不靠記憶）：
- ErEpr/*.lean（Axioms、Coupling 除外）：宣告名與行號（追 namespace／section）；
- 公理輸出（預設：evidence/ 底下最新一次 lake build 的 axioms.out）；
- tools/drills_manifest.json：每份演習的 expect；
- 最新一次 evidence/drills_*/results.json（若有）：實際紅名單；
- ErEpr/Coupling.lean：#assert_uses／#assert_not_uses。
同時檢查：每條定理都在 Axioms.lean 裡被 #print axioms（覆蓋率）。

用法：/usr/bin/python3 -I tools/gen_index.py [axioms.out 路徑]
"""
import json
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
SKIP = {"Axioms", "Coupling"}
ORDER = ["Basic", "NoSignalling", "TFD", "MPS", "Entropy", "NoGo", "Klein", "ER", "Hawking",
         "TensorNetwork", "Chain", "KMS", "KMSPair", "Charts", "MinCut", "Triangle", "Modular", "FirstLaw", "FirstLawGeneral", "GammaRotation", "Unruh", "Landauer", "Correlated", "Measurement", "Monogamy", "Swapping"]
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma)\s+([^\s(:{\[]+)")
NS = re.compile(r"^namespace\s+(\S+)")
SEC = re.compile(r"^(?:noncomputable\s+)?section\b")
END = re.compile(r"^end\b")
AX = re.compile(r"^'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
STD = "propext, Classical.choice, Quot.sound"
STD_SET = {"propext", "Classical.choice", "Quot.sound"}


def theorems(mod):
    out, stack = [], []
    for i, ln in enumerate((REPO / "ErEpr" / f"{mod}.lean").read_text(encoding="utf-8").splitlines(), 1):
        m = NS.match(ln)
        if m:
            stack.append(m.group(1).split("."))
            continue
        if SEC.match(ln):
            stack.append([])
            continue
        if END.match(ln) and stack:
            stack.pop()
            continue
        m = DECL.match(ln)
        if m:
            nm = m.group(2)
            full = nm[len("_root_."):] if nm.startswith("_root_.") else ".".join(
                [p for seg in stack for p in seg] + [nm])
            out.append((full, i))
    return out


def latest(pattern):
    c = sorted((REPO / "evidence").glob(pattern))
    return c[-1] if c else None


def main():
    axp = (pathlib.Path(sys.argv[1]).resolve() if len(sys.argv) > 1
           else latest("er_epr_*_lakebuild") / "axioms.out")
    ax = {}
    for ln in axp.read_text(encoding="utf-8").splitlines():
        m = AX.match(ln)
        if m:
            if m.group(3) is None:
                ax[m.group(1)] = "零公理"
            elif m.group(3) == STD:
                ax[m.group(1)] = "標準三公理"
            elif {x.strip() for x in m.group(3).split(",")} <= STD_SET:
                # 只用到標準三公理的一部分（例如 `decide` 證的小引理只用 propext）
                ax[m.group(1)] = f"標準公理子集（{m.group(3)}）"
            else:
                ax[m.group(1)] = m.group(3)
    manifest = json.loads((REPO / "tools" / "drills_manifest.json").read_text(encoding="utf-8"))
    hits = {}
    for d in manifest:
        for x in d["expect"]:
            hits.setdefault(x.split(".")[-1], []).append(d["name"])
    # 每份演習取最近一次重跑的結果（較新的目錄覆蓋較舊的）
    latest_run = {}
    for rd in sorted((REPO / "evidence").glob("drills_*")):
        if (rd / "results.json").exists():
            for r in json.loads((rd / "results.json").read_text(encoding="utf-8")):
                if "red" in r:
                    latest_run[r["name"]] = (rd.name, r["red"])
    red = {}
    for name, (_, reds) in latest_run.items():
        for x in reds:
            red.setdefault(x.split(".")[-1], []).append(name)
    runs = sorted({d for d, _ in latest_run.values()})
    coup = {}
    for ln in (REPO / "ErEpr" / "Coupling.lean").read_text(encoding="utf-8").splitlines():
        m = re.match(r"^#(assert_uses|assert_not_uses)\s+(\S+)\s+=>\s*(.*)$", ln)
        if m:
            tag = "⇒" if m.group(1) == "assert_uses" else "⇏"
            coup.setdefault(m.group(2).split(".")[-1], []).append(f"{tag} {m.group(3).strip()}")
    printed = set(re.findall(r"^#print axioms (\S+)", (REPO / "ErEpr" / "Axioms.lean").read_text(
        encoding="utf-8"), re.M))

    rows, total, missing_print, nonstd = [], 0, [], []
    for mod in ORDER:
        ths = theorems(mod)
        if not ths:
            continue
        rows += ["", f"## {mod}（{len(ths)} 條）", "",
                 "| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |", "|---|---|---|---|---|---|"]
        for full, line in ths:
            total += 1
            short = full.split(".")[-1]
            key = full if full.startswith("ErEpr.") else f"ErEpr.{full}"
            st = ax.get(key, "（無輸出）")
            if not (st in ("標準三公理", "零公理") or st.startswith("標準公理子集")):
                nonstd.append((key, st))
            if key[len("ErEpr."):] not in printed and full not in printed and short not in printed:
                missing_print.append(key)
            rows.append(
                f"| `{key[len('ErEpr.'):]}` | [{line}](../ErEpr/{mod}.lean#L{line}) | {st} | "
                f"{'、'.join(hits.get(short, []))} | {'、'.join(sorted(set(red.get(short, []))))} | "
                f"{'；'.join(coup.get(short, [])).replace('|', '¦')} |")
    head = [
        "# 定理索引（自動產生，勿手改）",
        "",
        "由 `tools/gen_index.py` 從磁碟產生。重新產生：`/usr/bin/python3 -I tools/gen_index.py`。",
        "",
        f"- 公理來源：`{axp.relative_to(REPO)}`",
        f"- 演習清單：`tools/drills_manifest.json`（{len(manifest)} 份）"
        + (f"；實際紅名單取每份演習最近一次重跑：{'、'.join(f'`evidence/{d}`' for d in runs)}" if runs else ""),
        f"- 定理總數：{total}（`theorem`／`lemma`，不含 `Axioms.lean`、`Coupling.lean`；不含 `def`、`example`）",
        f"- 公理狀態超出標準三公理的：{len(nonstd)} 條" + (
            "：" + "、".join(f"`{k}`（{v}）" for k, v in nonstd) if nonstd else ""),
        f"- 沒有被 `Axioms.lean` 印出公理的定理：{len(missing_print)} 條" + (
            "：" + "、".join(f"`{k}`" for k in missing_print) if missing_print else ""),
        "",
        "「演習（必須紅）」是清單上指定的；「實際紅」是最近一次重跑時，第一個失敗模組裡紅的宣告",
        "（多半比指定的多，因為下游定理連帶紅）。「耦合斷言」⇒＝依賴閉包必須含右邊；⇏＝不得含。",
    ]
    out = REPO / "docs" / "THEOREM_INDEX.md"
    out.write_text("\n".join(head + rows) + "\n", encoding="utf-8")
    print(f"{out}：{total} 條；非標準 {len(nonstd)}；未印公理 {len(missing_print)}")


if __name__ == "__main__":
    main()
