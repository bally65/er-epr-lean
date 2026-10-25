# 反向演習重跑報告 20261024T101303Z

清單：`tools/drills_manifest.json`（2 份）。通過 2/2。

原始碼快照 sha256（`ErEpr.lean`＋`ErEpr/*.lean`，所有演習樹都從它複製）：`cb51c15482c4be05da045642748c4b84ce1dc6171abc4e5d77e8d2113273adca`

判定：BASE 必須全綠；其他每份必須 rc ≠ 0、指定宣告都紅、反例區塊（若有）都綠。
紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停），所以下游模組的連帶紅不在表內。

| 演習 | 改動 | 結果 | 必須紅 | 實際紅（前 6） | 證據目錄 |
|---|---|---|---|---|---|
| BASE | （不改） | ✅ rc=0  | 全綠 |   | `er_epr_20261024T101303Z_rd_BASE` |
| FG3 | `FirstLawGeneral`: `HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (β * (tr` → `  obtain ⟨c, hc, hcq⟩ := exists_gibbs_lower hH β`<br>＋1 個反例區塊 | ✅ rc=1 FirstLawGeneral | `hasDerivAt_entropy_gibbsPath` | `hasDerivAt_entropy_gibbsPath`、`entanglement_first_law`  | `er_epr_20261024T101303Z_rd_FG3` |
