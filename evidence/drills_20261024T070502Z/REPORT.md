# 反向演習重跑報告 20261024T070502Z

清單：`tools/drills_manifest.json`（2 份）。通過 2/2。

原始碼快照 sha256（`ErEpr.lean`＋`ErEpr/*.lean`，所有演習樹都從它複製）：`156186497675d54913531dd8ff96ac579946a485fcd6fd8a66a6b0afd2488b28`

判定：BASE 必須全綠；其他每份必須 rc ≠ 0、指定宣告都紅、反例區塊（若有）都綠。
紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停），所以下游模組的連帶紅不在表內。

| 演習 | 改動 | 結果 | 必須紅 | 實際紅（前 6） | 證據目錄 |
|---|---|---|---|---|---|
| BASE | （不改） | ✅ rc=0  | 全綠 |   | `er_epr_20261024T070502Z_rd_BASE` |
| KL1 | `Klein`: `vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β)` → `vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β)`<br>＋1 個反例區塊 | ✅ rc=1 Klein | `vnEntropy_le_beta_energy_add_log` | `vnEntropy_le_beta_energy_add_log`、`vnEntropy_le_gibbs_of_energy_eq`、`vnEntropy_lt_gibbs_of_energy_eq`、`negctrl_klein_pure_H2`、`negctrl_klein_other_beta_H2`  | `er_epr_20261024T070502Z_rd_KL1` |
