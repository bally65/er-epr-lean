# 反向演習重跑報告 20261024T185634Z

清單：`tools/drills_manifest.json`（1 份）。通過 1/1。

原始碼快照 sha256（`ErEpr.lean`＋`ErEpr/*.lean`，所有演習樹都從它複製）：`4b09c2ddf267a0f9ec6292705e57210e5c0eabff4217698f6347e32e5dc85412`

判定：BASE 必須全綠；其他每份必須 rc ≠ 0、指定宣告都紅、反例區塊（若有）都綠。
紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停），所以下游模組的連帶紅不在表內。

| 演習 | 改動 | 結果 | 必須紅 | 實際紅（前 6） | 證據目錄 |
|---|---|---|---|---|---|
| SWP1 | `Swapping`: `(1 / 2 : ℂ) • vecMulVec (bellVecBC s t) (star (bellVecBC s t` → `(1 : ℂ) • vecMulVec (bellVecBC s t) (star (bellVecBC s t))`<br>＋1 個反例區塊 | ✅ rc=1 Swapping | `bellProjBC_mul_self`、`sum_bellProjBC` | `bellProjBC_mul_self`、`sum_bellProjBC`、`swapProj_eq_reindex`  | `er_epr_20261024T185634Z_rd_SWP1` |
