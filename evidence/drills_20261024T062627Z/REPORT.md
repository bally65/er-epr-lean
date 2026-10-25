# 反向演習重跑報告 20261024T062627Z

清單：`tools/drills_manifest.json`（4 份）。通過 4/4。

判定：BASE 必須全綠；其他每份必須 rc ≠ 0、指定宣告都紅、反例區塊（若有）都綠。
紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停），所以下游模組的連帶紅不在表內。

| 演習 | 改動 | 結果 | 必須紅 | 實際紅（前 6） | 證據目錄 |
|---|---|---|---|---|---|
| BASE | （不改） | ✅ rc=0  | 全綠 |   | `er_epr_20261024T062627Z_rd_BASE` |
| R1 | `Basic`: `Matrix.of fun i j => ∑ k, X (i, k) (j, k)` → `Matrix.of fun i j => ∑ k, X (j, k) (i, k)`<br>`Basic`: `ptrB X i j = ∑ k, X (i, k) (j, k) := rfl` → `ptrB X i j = ∑ k, X (j, k) (i, k) := rfl` | ✅ rc=1 Basic | `trace_ptrB_mul`、`ptrB_kronecker` | `ptrA_apply`、`ptrB_idKron_apply`、`trace_ptrB_mul`、`ptrB_kronecker`、`ptrB_posSemidef`、`ptrB_pure`  | `er_epr_20261024T062627Z_rd_R1` |
| K1 | `KMS`: `∀ a b : Matrix ι ι ℂ, trace (σ * a * nuStep H β b) = trace (` → `∀ a b : Matrix ι ι ℂ, trace (σ * a * b) = trace (σ * b * a)`<br>＋1 個反例區塊 | ✅ rc=1 KMS | `gibbs_isKMS`、`isKMS_unique` | `IsKMS`、`gibbs_isKMS`、`isKMS_unique`、`negctrl_scalar_not_kms`  | `er_epr_20261024T062627Z_rd_K1` |
| CP4 | `Coupling`: `#assert_not_uses ptrB_idKron => idKron_unique` → `#assert_not_uses ptrB_apply => idKron` | ✅ rc=1 Coupling | `#assert_not_uses ptrB_apply` | `#assert_not_uses ptrB_apply`  | `er_epr_20261024T062627Z_rd_CP4` |
