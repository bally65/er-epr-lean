#!/usr/bin/env python3
"""從歷史證據目錄重建反向演習清單（一次性產生器，留在 tools/ 當出處）。

每份演習的改動 = 演習副本 與 它當時的基準副本（演習前最後一次綠燈探針）逐行比對的差。
- 「替換／刪除」→ 一筆 edit（old → new），之後要能在【現行】檔案裡剛好找到一次；
- 檔尾插入的 example／theorem（「改壞後的陳述為假」的正面反例）→ append 區塊。
同時解析當年的 lean 輸出，列出當年紅在哪些宣告，供手挑 expect。

用法：/usr/bin/python3 -I tools/drills_extract.py > 草稿.json
（草稿再手挑 expect、補新演習，定稿成 tools/drills_manifest.json；見 tools/drills_finalize.py）
"""
import difflib
import json
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
EV = REPO / "evidence"

BASES = {
    ("R1", "R2", "R3", "R3b"): "20261023T104139Z_iter4",
    ("R4", "R5", "R6"): "20261023T105728Z_t2_iter3",
    ("R7", "R8", "R9"): "20261023T110437Z_t3_iter2",
    ("R10", "R11", "R12"): "20261023T111720Z_s2_iter4",
    ("R13", "R14", "R15"): "20261023T133204Z_er_iter3",
    ("R16", "R17", "R18"): "20261023T134558Z_hk_iter3",
    ("R19", "R20"): "20261023T142325Z_gap_iter4",
    ("TN1a", "TN1b", "TN2", "TN3"): "20261023T151054Z_C_iter3",
    ("NG1", "NG2", "NG3", "NG4", "COUPLE"): "20261023T165211Z_b1_iter2",
    ("E1", "K1", "K2", "P1", "T1"): "20261023T174850Z_b2_iter3",
    ("C1", "C2", "C3", "M1", "M2b", "G2"): "20261023T185820Z_b34_iter4",
}
ORDER = [n for names in BASES for n in names]
TAIL = "\nend\n\nend ErEpr\n"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\b\s*([^\s(:{\[]*)")
CMD = re.compile(r"^#(assert_uses|assert_not_uses)\s+(\S+)")
ERR = re.compile(r"^ErEpr/(\w+)\.lean:(\d+):\d+: error")


def base_of(name):
    for names, b in BASES.items():
        if name in names:
            return EV / f"er_epr_{b}"
    raise KeyError(name)


def drill_dir(name):
    ds = sorted(EV.glob(f"er_epr_*_drill_{name}"))
    return ds[-1]


def decl_at(lines, lineno):
    """第 lineno 行（1 起算）所在的宣告名；指令列回 `#指令 目標`。"""
    for i in range(lineno - 1, -1, -1):
        m = CMD.match(lines[i])
        if m:
            return f"#{m.group(1)} {m.group(2)}"
        m = DECL.match(lines[i])
        if m:
            kind, nm = m.group(1), m.group(2)
            return f"example@{i + 1}" if kind == "example" or not nm else nm
    return f"?@{lineno}"


def red_decls(ev_dir, src_dir=None):
    """證據目錄裡第一個失敗模組的錯誤，對回宣告名（以 src_dir 的副本為準）。"""
    src_dir = src_dir or ev_dir
    rec = (ev_dir / "receipt.txt").read_text(encoding="utf-8")
    failed = [m for m, rc in re.findall(r"^rc_(\w+)=(\d+)$", rec, re.M) if rc != "0"]
    out = {}
    for mod in failed:
        f = ev_dir / f"lean_{mod}.out"
        if not f.exists():
            continue
        lines = (src_dir / "ErEpr" / f"{mod}.lean").read_text(encoding="utf-8").splitlines()
        names = []
        for ln in f.read_text(encoding="utf-8", errors="replace").splitlines():
            m = ERR.match(ln)
            if m and m.group(1) == mod:
                d = decl_at(lines, int(m.group(2)))
                if d not in names:
                    names.append(d)
        out[mod] = names
    return out


def hunks(base_text, drill_text, cur_text):
    a = base_text.splitlines(keepends=True)
    b = drill_text.splitlines(keepends=True)
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    edits, appends = [], []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            continue
        old, new = "".join(a[i1:i2]), "".join(b[j1:j2])
        if tag == "insert" and "".join(a[i1:]).strip() in ("end\n\nend ErEpr".strip(), "end\n\nend ErEpr"):
            appends.append(new)
        elif tag == "insert":
            # 往回加上下文，直到在現行檔案裡唯一
            k = 1
            while k <= i1 and cur_text.count("".join(a[i1 - k:i1])) != 1:
                k += 1
            ctx = "".join(a[i1 - k:i1])
            edits.append({"old": ctx, "new": ctx + new})
        else:
            edits.append({"old": old, "new": new})
    return edits, appends


def main():
    manifest = []
    for name in ORDER:
        dd, bd = drill_dir(name), base_of(name)
        entry = {"name": name, "evidence": dd.name, "base": bd.name, "edits": [], "append": []}
        for f in sorted((dd / "ErEpr").glob("*.lean")):
            bf = bd / "ErEpr" / f.name
            if not bf.exists():
                continue
            bt, dt = bf.read_text(encoding="utf-8"), f.read_text(encoding="utf-8")
            if bt == dt:
                continue
            cur = (REPO / "ErEpr" / f.name).read_text(encoding="utf-8")
            edits, appends = hunks(bt, dt, cur)
            for e in edits:
                e["file"] = f"ErEpr/{f.name}"
                e["count_now"] = cur.count(e["old"])
                entry["edits"].append(e)
            for ap in appends:
                entry["append"].append({"file": f"ErEpr/{f.name}", "text": ap})
        entry["historical_red"] = red_decls(dd)
        manifest.append(entry)
    json.dump(manifest, sys.stdout, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
