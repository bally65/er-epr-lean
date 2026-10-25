#!/usr/bin/env python3
"""把 drills_extract.py 的草稿定稿成 tools/drills_manifest.json。

手挑的部分都寫在這裡（不改草稿）：
- EXPECT：每份演習【必須】紅的宣告（第一個失敗模組裡；取自 EVIDENCE.md 各節演習表）；
- OVERRIDE：原目標在後來改寫後已不存在的演習，重新指定改動（並說明為什麼）；
- EXTRA：歷史上沒有、這次新加的演習（S5、耦合檢驗本身）。
草稿裡的 append 區塊（「改壞後的陳述為假」的正面反例）原樣保留：跑演習時它們必須是綠的。

用法：/usr/bin/python3 -I tools/drills_extract.py > 草稿.json
      /usr/bin/python3 -I tools/drills_finalize.py 草稿.json   # 寫 tools/drills_manifest.json
"""
import json
import pathlib
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent

EXPECT = {
    "R1": ["trace_ptrB_mul", "ptrB_kronecker"],
    "R2": ["idKron_kronecker", "ptrB_idKron_apply"],
    "R3": ["ptrB_idKron"],
    "R3b": ["trace_toLin"],
    "R4": ["tfdAmp_conjTranspose", "tfdAmp_mul_conjTranspose"],
    "R5": ["gibbs_diagonal_real"],
    "R6": ["tfdAmp_conjTranspose"],
    "R7": ["rank_cutAt_mpsOpen_le"],
    "R8": ["rank_cutAt_mpsRing_le"],
    "R9": ["chainProd_append"],
    "R10": ["vnEntropy_le_log_rank"],
    "R11": ["vnEntropy_eq_sum_eigenvalues", "vnEntropy_diagonal"],
    "R12": ["vnEntropy_cut_mpsRing_le"],
    "R13": ["FutureCausal.nonneg"],
    "R14": ["throat_area_le"],
    "R15": ["inversion_isometry"],
    "R16": ["properDist_hasDerivAt"],
    "R17": ["conicalRatio_tendsto"],
    "R18": ["first_law_area"],
    "R19": ["transposeMap_not_completelyPositive"],
    "R20": ["tfd_boost_invariant"],
    "TN1a": ["rank_cutMat_tnAmp_le"],
    "TN1b": ["inW_of_inc_mem", "not_inW_of_inc_nmem"],
    "TN2": ["rank_cutMat_tnAmp_le"],
    "TN3": ["rank_cutMat_tnAmp_le"],
    "NG1": ["antitoneOn_gibbsEntropyFn"],
    "NG2": ["no_finite_dim_gibbs_matches_bh"],
    "NG3": ["negctrl_first_law_const"],
    "NG4": ["coneAngleRatio_cone"],
    "COUPLE": ["hawking_beta", "first_law_area"],
    "E1": ["tfdAmp_eq_exp"],
    "K1": ["gibbs_isKMS", "isKMS_unique"],
    "K2": ["isKMS_unique"],
    "P1": ["purification_unique_of_isUnit"],
    "T1": ["tracial_iff_period"],
    "C1": ["FK_mul_kf"],
    "C2": ["sliceX_inv"],
    "C3": ["boost_preserves_prod"],
    "M1": ["cutEdges_card_submodular"],
    "M2b": ["minCut_mmi"],
    "G2": ["rank_le_one_iff_vecMulVec"],
}

OVERRIDE = {
    # 歷史 R17 改的是 `Tendsto … (𝓝 1) ↔ β = 8πM`；B0 把它改寫成 `UnitConeAngle M β ↔ β = 8πM`，
    # 那一處現在就是 COUPLE 的目標。R17 改打分析核心：視界處極限值 β/8πM → β/4πM。
    "R17": {
        "edits": [{
            "file": "ErEpr/Hawking.lean",
            "old": "    Tendsto (conicalRatio M β) (𝓝[>] 0) (𝓝 (β / (8 * π * M))) := by\n",
            "new": "    Tendsto (conicalRatio M β) (𝓝[>] 0) (𝓝 (β / (4 * π * M))) := by\n",
        }],
        "note": "重新指定：原目標在 B0 改寫後與 COUPLE 同一處，改打 conicalRatio_tendsto 的極限值",
    },
}

EXTRA = [
    {
        "name": "BASE",
        "note": "對照組：不改任何東西，必須全綠（排除「紅是環境造成的」）",
        "edits": [], "append": [], "expect": [], "expect_green": True,
    },
    {
        "name": "S5",
        "note": "S5：dE/dβ 的負號拿掉（−Var → +Var）",
        "edits": [{
            "file": "ErEpr/NoGo.lean",
            "old": "    HasDerivAt (energyMean hH) (-energyVar hH β) β := by\n",
            "new": "    HasDerivAt (energyMean hH) (energyVar hH β) β := by\n",
        }],
        "append": [], "expect": ["hasDerivAt_energyMean", "gibbs_dS_eq_beta_dE"],
    },
    {
        "name": "CP1",
        "note": "耦合檢驗：加一條明顯錯的獨立性斷言（跨欄定理不依賴 ER 側），必須紅",
        "edits": [{
            "file": "ErEpr/Coupling.lean",
            "old": "#assert_not_uses antitoneOn_gibbsEntropyFn => hawking_beta first_law_area\n",
            "new": "#assert_not_uses antitoneOn_gibbsEntropyFn => hawking_beta first_law_area\n"
                   "#assert_not_uses no_gibbs_matches_first_law => hawking_beta\n",
        }],
        "append": [], "expect": ["#assert_not_uses no_gibbs_matches_first_law"],
    },
    {
        "name": "CP2",
        "note": "耦合檢驗：加一條明顯錯的依賴斷言（不可能定理用到 ER 側），必須紅",
        "edits": [{
            "file": "ErEpr/Coupling.lean",
            "old": "#assert_uses rank_cutMat_tnAmp_le => cutMat_tnAmp\n",
            "new": "#assert_uses rank_cutMat_tnAmp_le => cutMat_tnAmp\n"
                   "#assert_uses no_finite_dim_gibbs_matches_bh => hawking_beta\n",
        }],
        "append": [], "expect": ["#assert_uses no_finite_dim_gibbs_matches_bh"],
    },
    {
        "name": "CP3",
        "note": "耦合檢驗：閉包不展開定理的證明體（重現 2026-10-24 的第一版錯誤），依賴斷言必須紅",
        "edits": [{
            "file": "ErEpr/Coupling.lean",
            "old": "            | .thmInfo t => some t.value\n",
            "new": "            | .thmInfo _ => none\n",
        }],
        "append": [], "expect": ["#assert_uses first_law_area", "#assert_uses ptrB_tfdState"],
    },
    {
        "name": "CP4",
        "note": "耦合檢驗的空洞守門：對證明體裡沒有其他定理的 ptrB_apply（rfl）做獨立性斷言，必須判「不可信」而紅",
        "edits": [{
            "file": "ErEpr/Coupling.lean",
            "old": "#assert_not_uses ptrB_idKron => idKron_unique\n",
            "new": "#assert_not_uses ptrB_idKron => idKron_unique\n"
                   "#assert_not_uses ptrB_apply => idKron\n",
        }],
        "append": [], "expect": ["#assert_not_uses ptrB_apply"],
    },
    {
        "name": "KL1",
        "note": "Klein：右邊減 1（收緊）。反例：Gibbs 態本身取等號",
        "edits": [{
            "file": "ErEpr/Klein.lean",
            "old": "    vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β) := by\n",
            "new": "    vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β) - 1 := by\n",
        }],
        "append": [{"file": "ErEpr/Klein.lean", "text":
            "/-- 演習 KL1：收緊 1 之後的不等式為假（Gibbs 態取等號）。 -/\n"
            "example : ¬ ∀ σ : Matrix (Fin 2) (Fin 2) ℂ, σ.PosSemidef → trace σ = 1 →\n"
            "    vnEntropy σ ≤ Real.log 2 * (trace (σ * H2)).re +\n"
            "      Real.log (partZ H2_isHermitian (Real.log 2)) - 1 := by\n"
            "  intro h\n"
            "  have h1 := h (gibbs H2 (Real.log 2)) (gibbs_posSemidef H2_isHermitian _)\n"
            "    (trace_gibbs H2_isHermitian _)\n"
            "  rw [vnEntropy_gibbs_eq_beta_energy_add_log H2_isHermitian] at h1\n"
            "  linarith\n\n"}],
        "expect": ["vnEntropy_le_beta_energy_add_log"],
    },
    {
        "name": "KL2",
        "note": "Klein：逐項缺口的 (p − q) 改 (q − p)。反例：p = 0、q = 1",
        "edits": [{
            "file": "ErEpr/Klein.lean",
            "old": "def kleinGap (p q : ℝ) : ℝ := p * Real.log p - p * Real.log q - (p - q)\n",
            "new": "def kleinGap (p q : ℝ) : ℝ := p * Real.log p - p * Real.log q - (q - p)\n",
        }],
        "append": [{"file": "ErEpr/Klein.lean", "text":
            "/-- 演習 KL2：改壞的逐項不等式為假（p = 0、q = 1 時是 −1）。 -/\n"
            "example : ¬ ∀ p q : ℝ, 0 ≤ p → 0 < q → 0 ≤ kleinGap p q := by\n"
            "  intro h\n"
            "  have h1 := h 0 1 le_rfl one_pos\n"
            "  rw [kleinGap] at h1\n"
            "  norm_num at h1\n\n"}],
        "expect": ["kleinGap_nonneg", "kleinGap_pos"],
    },
    {
        "name": "KL3",
        "note": "Klein：拿掉 tr σ = 1",
        "edits": [{
            "file": "ErEpr/Klein.lean",
            "old": "    (hσ : σ.PosSemidef) (htr : trace σ = 1) :\n"
                   "    vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β) := by\n",
            "new": "    (hσ : σ.PosSemidef) :\n"
                   "    vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β) := by\n",
        }],
        "append": [], "expect": ["vnEntropy_le_beta_energy_add_log"],
    },
    {
        "name": "KL4",
        "note": "Klein 等號情形：σ = gibbs H β 改成 gibbs H (2β)",
        "edits": [{
            "file": "ErEpr/Klein.lean",
            "old": "    vnEntropy σ = β * (trace (σ * H)).re + Real.log (partZ hH β) ↔ σ = gibbs H β := by\n",
            "new": "    vnEntropy σ = β * (trace (σ * H)).re + Real.log (partZ hH β) ↔ "
                   "σ = gibbs H (2 * β) := by\n",
        }],
        "append": [], "expect": ["vnEntropy_eq_beta_energy_add_log_iff"],
    },
    {
        "name": "KL5",
        "note": "Klein：雙隨機恆等式拿掉行和為 1（只剩列隨機）",
        "edits": [{
            "file": "ErEpr/Klein.lean",
            "old": "    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1)\n"
                   "    (hq1 : ∑ j, q j = 1) (hp1 : ∑ i, p i = 1) :\n",
            "new": "    (hrow : ∀ i, ∑ j, M i j = 1)\n"
                   "    (hq1 : ∑ j, q j = 1) (hp1 : ∑ i, p i = 1) :\n",
        }],
        "append": [], "expect": ["klein_sum_identity"],
    },
    {
        "name": "TA1",
        "note": "T-a：Bekenstein 界的 2π 改 π。反例：M = 1",
        "edits": [{
            "file": "ErEpr/Triangle.lean",
            "old": "def bekensteinBound (R E : ℝ) : ℝ := 2 * π * R * E\n",
            "new": "def bekensteinBound (R E : ℝ) : ℝ := π * R * E\n",
        }],
        "append": [{"file": "ErEpr/Triangle.lean", "text":
            "/-- 演習 TA1：改壞後「黑洞填滿界」為假（M = 1 時 2π ≠ 4π）。 -/\n"
            "example : ¬ ∀ M : ℝ, 0 < M →\n"
            "    bekensteinBound (rOfRho M (M / 2)) M = areaIso M (M / 2) / 4 := by\n"
            "  intro h\n"
            "  have h1 := h 1 one_pos\n"
            "  rw [bekensteinBound, rOfRho_throat one_ne_zero, throat_area_eq one_pos] at h1\n"
            "  linarith [Real.pi_pos]\n\n"}],
        "expect": ["bekensteinBound_throat"],
    },
    {
        "name": "TB1",
        "note": "T-b：≤ 改 ≥。反例：熱庫終態 |0⟩⟨0|",
        "edits": [{
            "file": "ErEpr/Triangle.lean",
            "old": "    vnEntropy ρ - vnEntropy (gibbs H β) ≤\n"
                   "      β * ((trace (ρ * H)).re - (trace (gibbs H β * H)).re) := by\n",
            "new": "    vnEntropy ρ - vnEntropy (gibbs H β) ≥\n"
                   "      β * ((trace (ρ * H)).re - (trace (gibbs H β * H)).re) := by\n",
        }],
        "append": [{"file": "ErEpr/Triangle.lean", "text":
            "/-- 演習 TB1：反向的不等式為假（終態 |0⟩⟨0|，由 Klein 的嚴格版）。 -/\n"
            "example : ¬ ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → trace ρ = 1 →\n"
            "    vnEntropy ρ - vnEntropy (gibbs H2 (Real.log 2)) ≥\n"
            "      Real.log 2 * ((trace (ρ * H2)).re - (trace (gibbs H2 (Real.log 2) * H2)).re) := by\n"
            "  intro h\n"
            "  have h1 := h ket0Proj ket0Proj_posSemidef trace_ket0Proj\n"
            "  have h2 := negctrl_klein_pure_H2\n"
            "  have h3 := vnEntropy_gibbs_eq_beta_energy_add_log H2_isHermitian (Real.log 2)\n"
            "  linarith\n\n"}],
        "expect": ["reservoir_entropy_le_beta_heat"],
    },
    {
        "name": "TB2",
        "note": "T-b：拿掉熱庫終態半正定",
        "edits": [{
            "file": "ErEpr/Triangle.lean",
            "old": "    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :\n"
                   "    vnEntropy ρ - vnEntropy (gibbs H β) ≤\n",
            "new": "    (htr : trace ρ = 1) :\n"
                   "    vnEntropy ρ - vnEntropy (gibbs H β) ≤\n",
        }],
        "append": [], "expect": ["reservoir_entropy_le_beta_heat"],
    },
    {
        "name": "TE1",
        "note": "T-e：dE/dS 的 8πM 改 4πM",
        "edits": [{
            "file": "ErEpr/Triangle.lean",
            "old": "    HasDerivAt (fun s => Real.sqrt (s / (4 * π))) (1 / (8 * π * M)) (4 * π * M ^ 2) := by\n",
            "new": "    HasDerivAt (fun s => Real.sqrt (s / (4 * π))) (1 / (4 * π * M)) (4 * π * M ^ 2) := by\n",
        }],
        "append": [], "expect": ["hasDerivAt_bh_energy_of_entropy"],
    },
    {
        "name": "TC1",
        "note": "T-c：模哈密頓量的 −log 改 +log",
        "edits": [{
            "file": "ErEpr/Modular.lean",
            "old": "  U * diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ)) * star U\n",
            "new": "  U * diagonal (fun j => ((Real.log (q j) : ℝ) : ℂ)) * star U\n",
        }],
        "append": [], "expect": ["exp_neg_modHamOf", "relEntropyOf_diagonal"],
    },
    {
        "name": "TC2",
        "note": "T-c：拿掉 q > 0（主庫的 negctrl_modular_not_fullRank 已證拿掉後的特例為假）",
        "edits": [{
            "file": "ErEpr/Modular.lean",
            "old": "    (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)\n"
                   "    (htr : trace σ = 1) :\n"
                   "    vnEntropy σ - vnEntropy ρ₀ ≤\n",
            "new": "    (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)\n"
                   "    (htr : trace σ = 1) :\n"
                   "    vnEntropy σ - vnEntropy ρ₀ ≤\n",
        }],
        "append": [], "expect": ["entropy_le_modular"],
    },
    {
        "name": "TC3",
        "note": "T-c：古典 KL 的 log p − log q 對調",
        "edits": [{
            "file": "ErEpr/Modular.lean",
            "old": "      ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by\n",
            "new": "      ∑ i, p i * (Real.log (q i) - Real.log (p i)) := by\n",
        }],
        "append": [], "expect": ["relEntropyOf_diagonal"],
    },
    {
        "name": "FL1",
        "note": "第一定律：拿掉 Σv = 0（不保跡的方向）。反例：q = (1/2, 1/2)、v = (1, 1)",
        "edits": [{
            "file": "ErEpr/FirstLaw.lean",
            "old": "theorem entanglement_first_law_diag {q : ι → ℝ} (hq : ∀ i, 0 < q i) {v : ι → ℝ}\n"
                   "    (hv : ∑ i, v i = 0) :\n",
            "new": "theorem entanglement_first_law_diag {q : ι → ℝ} (hq : ∀ i, 0 < q i) {v : ι → ℝ} :\n",
        }],
        "append": [{"file": "ErEpr/FirstLaw.lean", "text":
            "/-- 演習 FL1：不保跡的方向上第一定律為假（差 Σv = 2）。 -/\n"
            "example : ¬ ∀ {q : Fin 2 → ℝ}, (∀ i, 0 < q i) → ∀ {v : Fin 2 → ℝ},\n"
            "    deriv (fun t => vnEntropy (diagPath q v t)) 0 =\n"
            "      deriv (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) 0 := by\n"
            "  intro h\n"
            "  have hq : ∀ i, (0 : ℝ) < ![1 / 2, 1 / 2] i := by\n"
            "    intro i\n"
            "    fin_cases i <;> norm_num\n"
            "  have h1 := @h ![1 / 2, 1 / 2] hq ![1, 1]\n"
            "  rw [(hasDerivAt_entropy_diagPath hq _).deriv, (hasDerivAt_modEnergy_diagPath _ _ _).deriv,\n"
            "    Fin.sum_univ_two, Fin.sum_univ_two] at h1\n"
            "  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1\n"
            "  linarith\n\n"}],
        "expect": ["entanglement_first_law_diag"],
    },
    {
        "name": "FL2",
        "note": "第一定律第二條路：結論改成 S′ = K′ + 1。反例由第一條路給出",
        "edits": [{
            "file": "ErEpr/FirstLaw.lean",
            "old": "    (hK : HasDerivAt (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) K' 0) :\n"
                   "    S' = K' := by\n",
            "new": "    (hK : HasDerivAt (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) K' 0) :\n"
                   "    S' = K' + 1 := by\n",
        }],
        "append": [{"file": "ErEpr/FirstLaw.lean", "text":
            "/-- 演習 FL2：改壞的第二條路為假（第一條路給出 S′ = K′）。 -/\n"
            "example : ¬ ∀ {q : Fin 2 → ℝ}, (∀ i, 0 < q i) → ∑ i, q i = 1 → ∀ {v : Fin 2 → ℝ},\n"
            "    ∑ i, v i = 0 → ∀ {S' K' : ℝ},\n"
            "    HasDerivAt (fun t => vnEntropy (diagPath q v t)) S' 0 →\n"
            "    HasDerivAt (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) K' 0 →\n"
            "    S' = K' + 1 := by\n"
            "  intro h\n"
            "  have hq : ∀ i, (0 : ℝ) < ![1 / 2, 1 / 2] i := by\n"
            "    intro i\n"
            "    fin_cases i <;> norm_num\n"
            "  have hq1 : ∑ i, ![(1 / 2 : ℝ), 1 / 2] i = 1 := by\n"
            "    rw [Fin.sum_univ_two]\n"
            "    norm_num\n"
            "  have hv : ∑ i, ![(1 : ℝ), -1] i = 0 := by\n"
            "    rw [Fin.sum_univ_two]\n"
            "    norm_num\n"
            "  have hS := hasDerivAt_entropy_diagPath hq ![1, -1]\n"
            "  have hK := hasDerivAt_modEnergy_diagPath ![1 / 2, 1 / 2] ![1, -1] ![1 / 2, 1 / 2]\n"
            "  have e1 := h hq hq1 hv hS hK\n"
            "  have e2 := entanglement_first_law_diag hq hv\n"
            "  rw [hS.deriv, hK.deriv] at e2\n"
            "  linarith\n\n"}],
        "expect": ["first_law_of_relEntropy_min"],
    },
    {
        "name": "FL3",
        "note": "負控制：把錯的參考 (2/3, 1/3) 換回同一個 (1/2, 1/2)。反例：第一定律本身",
        "edits": [{
            "file": "ErEpr/FirstLaw.lean",
            "old": "        modHamOf 1 ![2 / 3, 1 / 3])).re) 0 := by\n",
            "new": "        modHamOf 1 ![1 / 2, 1 / 2])).re) 0 := by\n",
        }],
        "append": [{"file": "ErEpr/FirstLaw.lean", "text":
            "/-- 演習 FL3：參考態相同時「δS ≠ δ⟨K⟩」為假（第一定律本身）。 -/\n"
            "example : ¬ (deriv (fun t => vnEntropy (diagPath ![1 / 2, 1 / 2] ![1, -1] t)) 0 ≠\n"
            "      deriv (fun t => (trace (diagPath ![1 / 2, 1 / 2] ![1, -1] t *\n"
            "        modHamOf 1 ![1 / 2, 1 / 2])).re) 0) := by\n"
            "  have hq : ∀ i, (0 : ℝ) < ![1 / 2, 1 / 2] i := by\n"
            "    intro i\n"
            "    fin_cases i <;> norm_num\n"
            "  have hv : ∑ i, ![(1 : ℝ), -1] i = 0 := by\n"
            "    rw [Fin.sum_univ_two]\n"
            "    norm_num\n"
            "  exact fun h => h (entanglement_first_law_diag hq hv)\n\n"}],
        "expect": ["negctrl_first_law_wrong_reference"],
    },
    {
        "name": "FG1",
        "note": "二次上界收緊一半：(p − q)²/q 改 (p − q)²/(2q)。反例：p = 0、q = 1",
        "edits": [{
            "file": "ErEpr/FirstLawGeneral.lean",
            "old": "theorem kleinGap_le_sq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : kleinGap p q ≤ (p - q) ^ 2 / q := by\n",
            "new": "theorem kleinGap_le_sq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :\n"
                   "    kleinGap p q ≤ (p - q) ^ 2 / (2 * q) := by\n",
        }],
        "append": [{"file": "ErEpr/FirstLawGeneral.lean", "text":
            "/-- 演習 FG1：收緊一半的逐項上界為假（p = 0、q = 1 時 1 ≤ 1/2）。 -/\n"
            "example : ¬ ∀ p q : ℝ, 0 ≤ p → 0 < q → kleinGap p q ≤ (p - q) ^ 2 / (2 * q) := by\n"
            "  intro h\n"
            "  have h1 := h 0 1 le_rfl one_pos\n"
            "  rw [kleinGap] at h1\n"
            "  norm_num at h1\n\n"}],
        "expect": ["kleinGap_le_sq"],
    },
    {
        "name": "FG2",
        "note": "拿掉 tr X = 0（不保跡的擾動）",
        "edits": [{
            "file": "ErEpr/FirstLawGeneral.lean",
            "old": "    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (hX0 : trace X = 0) :\n"
                   "    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (β * (trace (X * H)).re) 0 := by\n",
            "new": "    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :\n"
                   "    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (β * (trace (X * H)).re) 0 := by\n",
        }],
        "append": [], "expect": ["hasDerivAt_entropy_gibbsPath"],
    },
    {
        "name": "FG3",
        "note": "夾擠那條路的導數改成 2β·tr(XH)。反例由極小值那條路給出",
        "edits": [{
            "file": "ErEpr/FirstLawGeneral.lean",
            "old": "    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (β * (trace (X * H)).re) 0 := by\n"
                   "  obtain ⟨c, hc, hcq⟩ := exists_gibbs_lower hH β\n",
            "new": "    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (2 * β * (trace (X * H)).re) 0 := by\n"
                   "  obtain ⟨c, hc, hcq⟩ := exists_gibbs_lower hH β\n",
        }],
        "append": [{"file": "ErEpr/FirstLawGeneral.lean", "text":
            "/-- 演習 FG3：導數 2β·tr(XH) 為假（極小值那條路給出 β·tr(XH)；H2、β = ln 2、X = diag(1, −1)）。 -/\n"
            "example : ¬ ∀ {H : Matrix (Fin 2) (Fin 2) ℂ} (_ : H.IsHermitian) (β : ℝ)\n"
            "    {X : Matrix (Fin 2) (Fin 2) ℂ}, X.IsHermitian → trace X = 0 →\n"
            "    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (2 * β * (trace (X * H)).re) 0 := by\n"
            "  intro h\n"
            "  have hX : (diagonal fun i => ((![1, -1] i : ℝ) : ℂ)).IsHermitian := by\n"
            "    rw [Matrix.IsHermitian, diagonal_conjTranspose]\n"
            "    congr 1\n"
            "    funext i\n"
            "    simp\n"
            "  have hX0 : trace (diagonal fun i => ((![1, -1] i : ℝ) : ℂ)) = 0 := by\n"
            "    rw [trace_diagonal, Fin.sum_univ_two]\n"
            "    norm_num\n"
            "  have e := first_law_gibbs_of_hasDerivAt H2_isHermitian (Real.log 2) hX hX0\n"
            "    (h H2_isHermitian (Real.log 2) hX hX0)\n"
            "  have htr : (trace ((diagonal fun i => ((![1, -1] i : ℝ) : ℂ)) * H2)).re = -1 := by\n"
            "    norm_num [H2, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]\n"
            "  rw [htr] at e\n"
            "  have := Real.log_pos one_lt_two\n"
            "  linarith\n\n"}],
        "expect": ["hasDerivAt_entropy_gibbsPath"],
    },
    {
        "name": "FG4",
        "note": "負控制的參考態改成滿秩 (1/2, 1/2)。反例：此時對易版直接給出可微",
        "edits": [{
            "file": "ErEpr/FirstLawGeneral.lean",
            "old": "    ¬ DifferentiableAt ℝ (fun t => vnEntropy (diagPath ![1, 0] ![-1 / 2, 1 / 2] t)) 0 := by\n",
            "new": "    ¬ DifferentiableAt ℝ (fun t => vnEntropy (diagPath ![1 / 2, 1 / 2] ![-1 / 2, 1 / 2] t)) 0 := by\n",
        }],
        "append": [{"file": "ErEpr/FirstLawGeneral.lean", "text":
            "/-- 演習 FG4：參考態滿秩時「不可微」為假（影子存在）。 -/\n"
            "example : ¬ ¬ DifferentiableAt ℝ\n"
            "    (fun t => vnEntropy (diagPath ![1 / 2, 1 / 2] ![-1 / 2, 1 / 2] t)) 0 := by\n"
            "  have hq : ∀ i, (0 : ℝ) < ![1 / 2, 1 / 2] i := by\n"
            "    intro i\n"
            "    fin_cases i <;> norm_num\n"
            "  exact fun h => h (hasDerivAt_entropy_diagPath hq _).differentiableAt\n\n"}],
        "expect": ["negctrl_first_law_not_fullRank"],
    },
    {
        "name": "U1",
        "note": "X₁′：平均佔據數的 −1 改 +1（Bose 改 Fermi）",
        "edits": [{
            "file": "ErEpr/Unruh.lean",
            "old": "    meanOccupation β ω = 1 / (Real.exp (β * ω) - 1) := by\n",
            "new": "    meanOccupation β ω = 1 / (Real.exp (β * ω) + 1) := by\n",
        }],
        "append": [], "expect": ["meanOccupation_eq"],
    },
    {
        "name": "U2",
        "note": "X₁′：正則對易關係 |α|² − |β|² = 1 改成費米子的 |α|² + |β|² = 1。反例由費米負控制給出",
        "edits": [{
            "file": "ErEpr/Unruh.lean",
            "old": "    (hratio : B = Real.exp (-(2 * π / κ * ω)) * A) (hccr : A - B = 1) :\n",
            "new": "    (hratio : B = Real.exp (-(2 * π / κ * ω)) * A) (hccr : A + B = 1) :\n",
        }],
        "append": [{"file": "ErEpr/Unruh.lean", "text":
            "/-- 演習 U2：費米子的對易關係下「|β|² 是熱的玻色佔據數」為假。 -/\n"
            "example : ¬ ∀ {A B ω κ : ℝ}, 0 < κ → 0 < ω → B = Real.exp (-(2 * π / κ * ω)) * A →\n"
            "    A + B = 1 → B = meanOccupation (2 * π / κ) ω := by\n"
            "  intro h\n"
            "  have hx : 0 < Real.exp (-(2 * π / 1 * 1)) := Real.exp_pos _\n"
            "  have h1x : 1 + Real.exp (-(2 * π / 1 * 1)) ≠ 0 := by linarith\n"
            "  have hr : Real.exp (-(2 * π / 1 * 1)) * (1 / (1 + Real.exp (-(2 * π / 1 * 1)))) =\n"
            "      Real.exp (-(2 * π / 1 * 1)) * (1 / (1 + Real.exp (-(2 * π / 1 * 1)))) := rfl\n"
            "  have hc : 1 / (1 + Real.exp (-(2 * π / 1 * 1))) +\n"
            "      Real.exp (-(2 * π / 1 * 1)) * (1 / (1 + Real.exp (-(2 * π / 1 * 1)))) = 1 := by\n"
            "    field_simp\n"
            "  exact (negctrl_bogoliubov_fermi one_pos one_pos hr hc).2 (h one_pos one_pos hr hc)\n\n"}],
        "expect": ["bogoliubov_thermal"],
    },
    {
        "name": "U3",
        "note": "X₁′：表面重力 κ = 1/(4M) 改成 1/(2M)",
        "edits": [{
            "file": "ErEpr/Unruh.lean",
            "old": "    HasDerivAt (FS M) (2 * (1 / (4 * M))) (2 * M) := by\n",
            "new": "    HasDerivAt (FS M) (2 * (1 / (2 * M))) (2 * M) := by\n",
        }],
        "append": [], "expect": ["hasDerivAt_FS_horizon"],
    },
    {
        "name": "U4",
        "note": "X₁′：視界極限 e^{−πΩ} 改 e^{−2πΩ}",
        "edits": [{
            "file": "ErEpr/Unruh.lean",
            "old": "      (𝓝 (Real.exp (-(π * Ω)))) := by\n",
            "new": "      (𝓝 (Real.exp (-(2 * π * Ω)))) := by\n",
        }],
        "append": [], "expect": ["bogoliubov_ratio_tendsto"],
    },
    {
        "name": "U5",
        "note": "X₁′ 負控制：沒有視界時熱因子的極限 0 改 1",
        "edits": [{
            "file": "ErEpr/Unruh.lean",
            "old": "    Tendsto (fun κ : ℝ => Real.exp (-(2 * π / κ * ω))) (𝓝[>] 0) (𝓝 0) := by\n",
            "new": "    Tendsto (fun κ : ℝ => Real.exp (-(2 * π / κ * ω))) (𝓝[>] 0) (𝓝 1) := by\n",
        }],
        "append": [], "expect": ["negctrl_no_horizon"],
    },
    {
        "name": "U6",
        "note": "複數 Gamma 積分：(1/r)^a 改 r^a。反例由 mathlib 的實數速率版給出（a = 1、r = 2）",
        "edits": [{
            "file": "ErEpr/GammaRotation.lean",
            "old": "    ∫ t in Ioi (0 : ℝ), gammaKernel a r t = (1 / r) ^ a * Complex.Gamma a := by\n",
            "new": "    ∫ t in Ioi (0 : ℝ), gammaKernel a r t = r ^ a * Complex.Gamma a := by\n",
        }],
        "append": [{"file": "ErEpr/GammaRotation.lean", "text":
            "/-- 演習 U6：改壞的 Gamma 積分為假（a = 1、r = 2：左邊 1/2，右邊 2）。 -/\n"
            "example : ¬ ∀ {a r : ℂ}, 0 < a.re → 0 < r.re →\n"
            "    ∫ t in Ioi (0 : ℝ), gammaKernel a r t = r ^ a * Complex.Gamma a := by\n"
            "  intro h\n"
            "  have h1 := @h 1 ((2 : ℝ) : ℂ) (by norm_num) (by norm_num)\n"
            "  have h2 : ∫ t in Ioi (0 : ℝ), gammaKernel 1 ((2 : ℝ) : ℂ) t =\n"
            "      (1 / ((2 : ℝ) : ℂ)) ^ (1 : ℂ) * Complex.Gamma 1 :=\n"
            "    integral_cpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)\n"
            "  rw [h1, Complex.Gamma_one, Complex.cpow_one, Complex.cpow_one] at h2\n"
            "  norm_num at h2\n\n"}],
        "expect": ["integral_gammaKernel"],
    },
    {
        "name": "LD1",
        "note": "T-d：次可加性拿掉跡為 1（主庫的 negctrl_subadditive_unnormalized 已證拿掉後為假）",
        "edits": [{
            "file": "ErEpr/Landauer.lean",
            "old": "theorem vnEntropy_subadditive {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : ρ.PosSemidef)\n"
                   "    (htr : trace ρ = 1) : vnEntropy ρ ≤ vnEntropy (ptrB ρ) + vnEntropy (ptrA ρ) := by\n",
            "new": "theorem vnEntropy_subadditive {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : ρ.PosSemidef) :\n"
                   "    vnEntropy ρ ≤ vnEntropy (ptrB ρ) + vnEntropy (ptrA ρ) := by\n",
        }],
        "append": [{"file": "ErEpr/Landauer.lean", "text":
            "/-- 演習 LD1：不要求跡為 1 的次可加性為假（ρ = 2·1，一維 ⊗ 一維）。 -/\n"
            "example : ¬ ∀ {ρ : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ}, ρ.PosSemidef →\n"
            "    vnEntropy ρ ≤ vnEntropy (ptrB ρ) + vnEntropy (ptrA ρ) := by\n"
            "  intro h\n"
            "  have hpsd : (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)).PosSemidef := by\n"
            "    rw [smul_one_eq_diagonal]\n"
            "    exact posSemidef_diagonal_iff.mpr fun _ => Complex.zero_le_real.mpr (by norm_num)\n"
            "  exact negctrl_subadditive_unnormalized (h hpsd)\n\n"}],
        "expect": ["vnEntropy_subadditive"],
    },
    {
        "name": "LD2",
        "note": "T-d：熱的正負號反過來（熱庫放熱也能抹除）。反例：交換見證",
        "edits": [{
            "file": "ErEpr/Landauer.lean",
            "old": "      β * ((trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re -\n"
                   "        (trace (gibbs H β * H)).re) := by\n"
                   "  have hγ := gibbs_posSemidef hH β\n",
            "new": "      β * ((trace (gibbs H β * H)).re -\n"
                   "        (trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re) := by\n"
                   "  have hγ := gibbs_posSemidef hH β\n",
        }],
        "append": [{"file": "ErEpr/Landauer.lean", "text":
            "/-- 演習 LD2：熱的正負號反過來為假（交換見證：系統熵嚴格減少、熱庫嚴格吸熱）。 -/\n"
            "example : ¬ ∀ {ρS : Matrix (Fin 2) (Fin 2) ℂ}, ρS.PosSemidef → trace ρS = 1 →\n"
            "    ∀ {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}, star U * U = 1 →\n"
            "    vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H2 (Real.log 2)) * star U)) ≤\n"
            "      Real.log 2 * ((trace (gibbs H2 (Real.log 2) * H2)).re -\n"
            "        (trace (ptrA (U * (ρS ⊗ₖ gibbs H2 (Real.log 2)) * star U) * H2)).re) := by\n"
            "  intro h\n"
            "  have h1 := @h mix2 mix2_posSemidef trace_mix2 (swapU (Fin 2)) swapU_star_mul\n"
            "  obtain ⟨hS, hQ⟩ := landauer_swap_witness\n"
            "  have hl := Real.log_pos one_lt_two\n"
            "  nlinarith\n\n"}],
        "expect": ["landauer"],
    },
    {
        "name": "LD3",
        "note": "T-d：拿掉么正性（主庫的 negctrl_landauer_not_unitary 已證拿掉後為假）",
        "edits": [{
            "file": "ErEpr/Landauer.lean",
            "old": "    {H : Matrix κ κ ℂ} (hH : H.IsHermitian) (β : ℝ) {U : Matrix (ι × κ) (ι × κ) ℂ}\n"
                   "    (hU : star U * U = 1) :\n"
                   "    vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H β) * star U)) ≤\n",
            "new": "    {H : Matrix κ κ ℂ} (hH : H.IsHermitian) (β : ℝ) {U : Matrix (ι × κ) (ι × κ) ℂ} :\n"
                   "    vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H β) * star U)) ≤\n",
        }],
        "append": [{"file": "ErEpr/Landauer.lean", "text":
            "/-- 演習 LD3：不要求么正的 Landauer 為假（非么正重置 resetS ⊗ 1）。 -/\n"
            "example : ¬ ∀ {ρS : Matrix (Fin 2) (Fin 2) ℂ}, ρS.PosSemidef → trace ρS = 1 →\n"
            "    ∀ {U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ},\n"
            "    vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H2 (Real.log 2)) * star U)) ≤\n"
            "      Real.log 2 * ((trace (ptrA (U * (ρS ⊗ₖ gibbs H2 (Real.log 2)) * star U) * H2)).re -\n"
            "        (trace (gibbs H2 (Real.log 2) * H2)).re) := fun h =>\n"
            "  negctrl_landauer_not_unitary H2_isHermitian (Real.log 2)\n"
            "    (@h mix2 mix2_posSemidef trace_mix2 (resetS ⊗ₖ 1))\n\n"}],
        "expect": ["landauer"],
    },
    {
        "name": "LD4",
        "note": "T-d：參考態不往均勻分佈混（ε/d 拿掉），不滿秩時 Klein 用不上",
        "edits": [{
            "file": "ErEpr/Landauer.lean",
            "old": "def mixUnif (ε : ℝ) (a : ι → ℝ) (i : ι) : ℝ := (1 - ε) * a i + ε / Fintype.card ι\n",
            "new": "def mixUnif (ε : ℝ) (a : ι → ℝ) (i : ι) : ℝ := (1 - ε) * a i\n",
        }],
        "append": [{"file": "ErEpr/Landauer.lean", "text":
            "/-- 演習 LD4：只縮不混時參考態可以不滿秩（a = 0 時 (1 − ε)·a = 0）。 -/\n"
            "example : ¬ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ a : Fin 2 → ℝ, (∀ i, 0 ≤ a i) →\n"
            "    ∀ i, 0 < (1 - ε) * a i := by\n"
            "  intro h\n"
            "  have h0 := h 1 one_pos le_rfl 0 (fun _ => le_rfl) 0\n"
            "  simp at h0\n\n"}],
        "expect": ["mixUnif_pos"],
    },
    {
        "name": "BL1",
        "note": "糾纏起點：Bell 基底矩陣拿掉負號（Φ⁻、Ψ⁻ 變成 Φ⁺、Ψ⁺），不再是 √2 倍么正矩陣",
        "edits": [{
            "file": "ErEpr/Correlated.lean",
            "old": "  Matrix.of fun p q => if (p.1 = p.2 ↔ q.1 = q.2) then (if p.1 = 1 ∧ q.1 = 1 then -1 else 1) else 0\n",
            "new": "  Matrix.of fun p q => if (p.1 = p.2 ↔ q.1 = q.2) then 1 else 0\n",
        }],
        "append": [{"file": "ErEpr/Correlated.lean", "text":
            "/-- 演習 BL1：拿掉負號後 K² = 2 為假（(00, 11) 那一格是 2 不是 0）。 -/\n"
            "example : ¬ (bellK * bellK = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by\n"
            "  intro h\n"
            "  have h1 := congrFun (congrFun h (0, 0)) (1, 1)\n"
            "  norm_num [bellK, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h1\n\n"}],
        "expect": ["bellK_mul_self", "bellK_conj_maxEnt"],
    },
    {
        "name": "BL2",
        "note": "糾纏起點：把「乘積起點不能抹除」的起點換成 Bell 態。反例：解糾纏一步歸零",
        "edits": [{
            "file": "ErEpr/Correlated.lean",
            "old": "      Real.log 2 ≤\n"
                   "        vnEntropy (ptrB (U * (mix2 ⊗ₖ gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β) * star U))) ∧\n",
            "new": "      Real.log 2 ≤\n"
                   "        vnEntropy (ptrB (U * maxEnt (Fin 2) * star U))) ∧\n",
        }],
        "append": [{"file": "ErEpr/Correlated.lean", "text":
            "/-- 演習 BL2：Bell 起點時「任何么正演化後系統熵仍 ≥ ln 2」為假。 -/\n"
            "example : ¬ ∀ U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, star U * U = 1 →\n"
            "    Real.log 2 ≤ vnEntropy (ptrB (U * maxEnt (Fin 2) * star U)) := by\n"
            "  intro h\n"
            "  have h1 := h disentangle disentangle_star_mul\n"
            "  rw [ptrB_disentangle_bell, vnEntropy_ket0Proj] at h1\n"
            "  linarith [Real.log_pos one_lt_two]\n\n"}],
        "expect": ["correlation_is_fuel"],
    },
    {
        "name": "BL3",
        "note": "古典對照拿掉「對角」：S(A) ≤ S(AB) 推廣到任何量子態。反例：Bell 態",
        "edits": [{
            "file": "ErEpr/Correlated.lean",
            "old": "theorem vnEntropy_ptrB_diagonal_le (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) :\n"
                   "    vnEntropy (ptrB (diagonal fun x => (p x : ℂ))) ≤ vnEntropy (diagonal fun x => (p x : ℂ)) := by\n",
            "new": "theorem vnEntropy_ptrB_diagonal_le (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef)\n"
                   "    (htr : trace ρ = 1) : vnEntropy (ptrB ρ) ≤ vnEntropy ρ := by\n",
        }],
        "append": [{"file": "ErEpr/Correlated.lean", "text":
            "/-- 演習 BL3：量子態的 S(A) ≤ S(AB) 為假（Bell 態：ln 2 > 0）。 -/\n"
            "example : ¬ ∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → trace ρ = 1 →\n"
            "    vnEntropy (ptrB ρ) ≤ vnEntropy ρ := by\n"
            "  intro h\n"
            "  have hpsd : (maxEnt (Fin 2)).PosSemidef := by\n"
            "    rw [maxEnt_eq_disentangle_conj, star_eq_conjTranspose]\n"
            "    exact (ket0Proj_posSemidef.kronecker ket0Proj_posSemidef).mul_mul_conjTranspose_same _\n"
            "  have htr : trace (maxEnt (Fin 2)) = 1 := by\n"
            "    rw [← trace_ptrB, ptrB_bell_eq_mix2, trace_mix2]\n"
            "  exact negctrl_entropy_monotone (h _ hpsd htr)\n\n"}],
        "expect": ["vnEntropy_ptrB_diagonal_le"],
    },
    {
        "name": "MS1",
        "note": "觀測：CNOT 的控制位元反過來（控制為 0 時才翻）。|+⟩|0⟩ 變成 Ψ⁺，不是 Bell 態 Φ⁺",
        "edits": [{
            "file": "ErEpr/Measurement.lean",
            "old": "  Matrix.of fun p q => if p.1 = q.1 ∧ (p.2 = q.2 ↔ q.1 = 0) then 1 else 0\n",
            "new": "  Matrix.of fun p q => if p.1 = q.1 ∧ (p.2 = q.2 ↔ q.1 = 1) then 1 else 0\n",
        }],
        "append": [{"file": "ErEpr/Measurement.lean", "text":
            "/-- 演習 MS1：控制反過來時測量結果不是 Bell 態（(00, 00) 那一格是 0 不是 1/2）。 -/\n"
            "example : ¬ (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot = maxEnt (Fin 2)) := by\n"
            "  intro h\n"
            "  have h1 := congrFun (congrFun h (0, 0)) (0, 0)\n"
            "  norm_num [cnot, plusProj, ket0Proj, maxEnt, Matrix.mul_apply, Fintype.sum_prod_type,\n"
            "    Fin.sum_univ_two, kroneckerMap_apply, vecMulVec_apply, Matrix.star_apply] at h1\n\n"}],
        "expect": ["cnot_measure"],
    },
    {
        "name": "MS2",
        "note": "觀測：宣稱只動系統就能解開（熵回到 0）。反例：U = 1",
        "edits": [{
            "file": "ErEpr/Measurement.lean",
            "old": "        star (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = Real.log 2 := by\n"
                   "  rw [ptrB_local_conj, vnEntropy_unitary_conj _ _ hU, ptrB_after, vnEntropy_mix2]\n",
            "new": "        star (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = 0 := by\n"
                   "  rw [ptrB_local_conj, vnEntropy_unitary_conj _ _ hU, ptrB_after, vnEntropy_mix2]\n",
        }],
        "append": [{"file": "ErEpr/Measurement.lean", "text":
            "/-- 演習 MS2：「只動系統就能讓熵回到 0」為假（U = 1 時熵是 ln 2）。 -/\n"
            "example : ¬ ∀ {U : Matrix (Fin 2) (Fin 2) ℂ}, star U * U = 1 →\n"
            "    vnEntropy (ptrB ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *\n"
            "      (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) *\n"
            "        star (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = 0 := by\n"
            "  intro h\n"
            "  have h1 := @h 1 (by simp)\n"
            "  rw [one_kronecker_one, star_one, Matrix.one_mul, Matrix.mul_one, ptrB_after,\n"
            "    vnEntropy_mix2] at h1\n"
            "  exact (Real.log_pos one_lt_two).ne' h1\n\n"}],
        "expect": ["local_cannot_undo"],
    },
    {
        "name": "MS3",
        "note": "觀測：宣稱只動儀器就能解開。反例：Pauli X 通道（不可通訊）",
        "edits": [{
            "file": "ErEpr/Measurement.lean",
            "old": "    vnEntropy (ptrB (Φ.app (Fin 2) (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot))) = Real.log 2 := by\n",
            "new": "    vnEntropy (ptrB (Φ.app (Fin 2) (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot))) = 0 := by\n",
        }],
        "append": [{"file": "ErEpr/Measurement.lean", "text":
            "/-- 演習 MS3：「只動儀器就能讓熵回到 0」為假（Pauli X 通道之後熵仍是 ln 2）。 -/\n"
            "example : ¬ (vnEntropy (ptrB (krausX.app (Fin 2)\n"
            "    (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot))) = 0) := by\n"
            "  rw [Kraus.no_signalling, ptrB_after, vnEntropy_mix2]\n"
            "  exact (Real.log_pos one_lt_two).ne'\n\n"}],
        "expect": ["pointer_cannot_undo"],
    },
    {
        "name": "MG1",
        "note": "一夫一妻：拿掉「AB 的邊際是純態」（主庫的 negctrl_monogamy_mixed 已證拿掉後為假）",
        "edits": [{
            "file": "ErEpr/Monogamy.lean",
            "old": "    (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1)\n"
                   "    (hpure : ptrB ρ = c • vecMulVec v (star v)) :\n"
                   "    ρ = ptrB ρ ⊗ₖ ptrA ρ := by\n",
            "new": "    (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1) :\n"
                   "    ρ = ptrB ρ ⊗ₖ ptrA ρ := by\n",
        }],
        "append": [{"file": "ErEpr/Monogamy.lean", "text":
            "/-- 演習 MG1：不要求邊際是純態時「整體是乘積」為假（Bell 態看成 qubit ⊗ qubit）。 -/\n"
            "example : ¬ ∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef →\n"
            "    ρ = ptrB ρ ⊗ₖ ptrA ρ := fun h => negctrl_monogamy_mixed (h _ maxEnt_posSemidef)\n\n"}],
        "expect": ["monogamy"],
    },
    {
        "name": "MG2",
        "note": "一夫一妻：宣稱 Bell 時 A 與 C 的互資訊是 2 ln 2。反例：Bell ⊗ |0⟩⟨0|",
        "edits": [{
            "file": "ErEpr/Monogamy.lean",
            "old": "      vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA ρ) - vnEntropy (ptrMid ρ) = 0 := by\n"
                   "  have hcs",
            "new": "      vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA ρ) - vnEntropy (ptrMid ρ) = 2 * Real.log 2 := by\n"
                   "  have hcs",
        }],
        "append": [{"file": "ErEpr/Monogamy.lean", "text":
            "/-- 演習 MG2：「A 與 C 的互資訊是 2 ln 2」為假（Bell ⊗ |0⟩⟨0| 時是 0）。 -/\n"
            "example : ¬ ∀ {ρ : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ},\n"
            "    ρ.PosSemidef → ptrB ρ = maxEnt (Fin 2) →\n"
            "    vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA ρ) - vnEntropy (ptrMid ρ) = 2 * Real.log 2 := by\n"
            "  intro h\n"
            "  obtain ⟨hpsd, hB⟩ := bell_monogamy_witness\n"
            "  have h1 := h hpsd hB\n"
            "  have hcs : star ((Fintype.card (Fin 2) : ℂ))⁻¹ = ((Fintype.card (Fin 2) : ℂ))⁻¹ := by simp\n"
            "  have h0 := (monogamy_mutualInfo hpsd hcs bell_rankOne_norm (hB.trans rfl)).2\n"
            "  rw [h0] at h1\n"
            "  linarith [Real.log_pos one_lt_two]\n\n"}],
        "expect": ["bell_monogamy"],
    },
    {
        "name": "MG3",
        "note": "一夫一妻：區塊計算裡 v、w 對調",
        "edits": [{
            "file": "ErEpr/Monogamy.lean",
            "old": "      vecMulVec v w ⊗ₖ (Matrix.of fun a b => ∑ n, ∑ n', w n * ρ (n, a) (n', b) * v n') := by\n",
            "new": "      vecMulVec v w ⊗ₖ (Matrix.of fun a b => ∑ n, ∑ n', v n * ρ (n, a) (n', b) * w n') := by\n",
        }],
        "append": [], "expect": ["rankOne_kron_one_conj"],
    },
    {
        "name": "SW1",
        "note": "糾纏交換：B、C 的投影拿掉「聯合」的條件（不再是 Bell 投影）",
        "edits": [{
            "file": "ErEpr/Swapping.lean",
            "old": "    if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 ∧ p.2.1 = p.1.2 + t ∧ q.2.1 = q.1.2 + t then\n",
            "new": "    if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 then\n",
        }],
        "append": [], "expect": ["swapProj_mulVec"],
    },
    {
        "name": "SW2",
        "note": "糾纏交換：宣稱 Φ⁺ 結果的機率是 1/2。反例：swap_prob",
        "edits": [{
            "file": "ErEpr/Swapping.lean",
            "old": "    trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) = 1 / 4 ∧\n"
                   "      (trace (swapProj 0 0",
            "new": "    trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) = 1 / 2 ∧\n"
                   "      (trace (swapProj 0 0",
        }],
        "append": [{"file": "ErEpr/Swapping.lean", "text":
            "/-- 演習 SW2：Φ⁺ 結果的機率是 1/2 為假（是 1/4）。 -/\n"
            "example : ¬ (trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) =\n"
            "    1 / 2) := by\n"
            "  rw [swap_prob]\n"
            "  norm_num\n\n"}],
        "expect": ["entanglement_swapping"],
    },
    {
        "name": "SW3",
        "note": "糾纏交換：宣稱四結果平均之後 A–D 就是 Bell 態（可以傳訊息）。反例：平均是 ½·1 ⊗ ½·1",
        "edits": [{
            "file": "ErEpr/Swapping.lean",
            "old": "      ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) := by\n"
                   "  rw [swap_average_eq, swap_before.1]\n",
            "new": "      maxEnt (Fin 2) := by\n"
                   "  rw [swap_average_eq, swap_before.1]\n",
        }],
        "append": [{"file": "ErEpr/Swapping.lean", "text":
            "/-- 演習 SW3：四結果平均之後 A–D 是 Bell 態為假（(00, 11) 那一格是 0 不是 1/2）。 -/\n"
            "example : ¬ (∑ s : Fin 2, ∑ t : Fin 2,\n"
            "    ptrBC (swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t) =\n"
            "      maxEnt (Fin 2)) := by\n"
            "  rw [swap_average_eq]\n"
            "  intro h\n"
            "  have h1 := congrFun (congrFun h (0, 0)) (1, 1)\n"
            "  norm_num [mix2, maxEnt, kroneckerMap_apply, vecMulVec_apply, Matrix.one_apply] at h1\n\n"}],
        "expect": ["swap_average_no_signalling"],
    },
    {
        "name": "AF1",
        "note": "AMPS：拿掉「A–B 是純態」。反例：GHZ（主庫的 negctrl_amps_mixed）",
        "edits": [{
            "file": "ErEpr/Swapping.lean",
            "old": "    {c : ℂ} {v : ι × κ → ℂ} (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1)\n"
                   "    (hpure : ptrB ρ = c • vecMulVec v (star v)) :\n"
                   "    ptrFirst ρ = ptrA (ptrB ρ) ⊗ₖ ptrA ρ ∧ mutualInfo (ptrFirst ρ) = 0 := by\n",
            "new": "    {c : ℂ} {v : ι × κ → ℂ} (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1) :\n"
                   "    ptrFirst ρ = ptrA (ptrB ρ) ⊗ₖ ptrA ρ ∧ mutualInfo (ptrFirst ρ) = 0 := by\n",
        }],
        "append": [{"file": "ErEpr/Swapping.lean", "text":
            "/-- 演習 AF1：不要求 A–B 是純態時「B 與 R 不相關」為假（GHZ：I(B:R) = ln 2）。 -/\n"
            "example : ¬ ∀ ρ : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ,\n"
            "    ρ.PosSemidef → mutualInfo (ptrFirst ρ) = 0 := by\n"
            "  intro h\n"
            "  obtain ⟨hpsd, -, hpos⟩ := negctrl_amps_mixed\n"
            "  exact hpos.ne' (h _ hpsd)\n\n"}],
        "expect": ["amps_monogamy"],
    },
    {
        "name": "NG5",
        "note": "不可能定理的負控制：量詞換成「∃ 一個固定的 H 對所有 β」。反例：不可能定理本身",
        "edits": [{
            "file": "ErEpr/NoGo.lean",
            "old": "    ∃ n : ℕ, ∀ β ∈ Set.Ioo a b, ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,\n"
                   "      H.IsHermitian ∧ vnEntropy (gibbs H β) = β ^ 2 / (16 * π) := by\n"
                   "  refine ⟨⌈Real.exp",
            "new": "    ∃ n : ℕ, ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,\n"
                   "      H.IsHermitian ∧ ∀ β ∈ Set.Ioo a b, vnEntropy (gibbs H β) = β ^ 2 / (16 * π) := by\n"
                   "  refine ⟨⌈Real.exp",
        }],
        "append": [{"file": "ErEpr/NoGo.lean", "text":
            "/-- 演習 NG5：「一個固定的 H 對整段 β 都對得上」為假（就是不可能定理）。 -/\n"
            "example : ¬ ∃ n : ℕ, ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,\n"
            "    H.IsHermitian ∧ ∀ β ∈ Set.Ioo (1 : ℝ) 2, vnEntropy (gibbs H β) = β ^ 2 / (16 * π) := by\n"
            "  rintro ⟨n, H, hH, h⟩\n"
            "  exact no_finite_dim_gibbs_matches_bh hH one_pos one_lt_two h\n\n"}],
        "expect": ["negctrl_nogo_varying_hamiltonian"],
    },
    {
        "name": "NG6",
        "note": "不可能定理的負控制：拿掉 β ≠ 0。反例：β = 0 時 Gibbs 態是最大混合態，熵固定是 log d",
        "edits": [{
            "file": "ErEpr/NoGo.lean",
            "old": "theorem exists_hamiltonian_gibbs_entropy_eq (n : ℕ) {β : ℝ} (hβ : β ≠ 0) {s : ℝ} (hs0 : 0 < s)\n",
            "new": "theorem exists_hamiltonian_gibbs_entropy_eq (n : ℕ) {β : ℝ} {s : ℝ} (hs0 : 0 < s)\n",
        }],
        "append": [{"file": "ErEpr/NoGo.lean", "text":
            "/-- 演習 NG6：β = 0 時「熵可以調成任何 s」為假（熵固定是 log 2）。 -/\n"
            "example : ¬ ∀ s : ℝ, 0 < s → s < Real.log 2 →\n"
            "    ∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian ∧ vnEntropy (gibbs H 0) = s := by\n"
            "  intro h\n"
            "  have hl := Real.log_pos one_lt_two\n"
            "  obtain ⟨H, -, hS⟩ := h (Real.log 2 / 2) (by linarith) (by linarith)\n"
            "  rw [vnEntropy_gibbs_zero, Fintype.card_fin] at hS\n"
            "  push_cast at hS\n"
            "  linarith\n\n"}],
        "expect": ["exists_hamiltonian_gibbs_entropy_eq"],
    },
    {
        "name": "SWP1",
        "note": "Π 是投影：B、C 上的投影少了 1/2（不再歸一）。反例：P² = 2P",
        "edits": [{
            "file": "ErEpr/Swapping.lean",
            "old": "  (1 / 2 : ℂ) • vecMulVec (bellVecBC s t) (star (bellVecBC s t))\n",
            "new": "  (1 : ℂ) • vecMulVec (bellVecBC s t) (star (bellVecBC s t))\n",
        }],
        "append": [{"file": "ErEpr/Swapping.lean", "text":
            "/-- 演習 SWP1：少了 1/2 時不是投影（(00, 00) 那一格：P² 是 2，P 是 1）。 -/\n"
            "example : ¬ (bellProjBC 0 0 * bellProjBC 0 0 = bellProjBC 0 0) := by\n"
            "  intro h\n"
            "  have h1 := congrFun (congrFun h (0, 0)) (0, 0)\n"
            "  norm_num [bellProjBC, bellVecBC, bellSign, vecMulVec_apply, Matrix.mul_apply,\n"
            "    Fintype.sum_prod_type, Fin.sum_univ_two] at h1\n\n"}],
        "expect": ["bellProjBC_mul_self", "sum_bellProjBC"],
    },
    {
        "name": "LOC1",
        "note": "只動系統：一般維度的約化公式把 U 與 Uᴴ 對調",
        "edits": [{
            "file": "ErEpr/Measurement.lean",
            "old": "    ptrB ((U ⊗ₖ (1 : Matrix κ κ ℂ)) * X * star (U ⊗ₖ (1 : Matrix κ κ ℂ))) = U * ptrB X * star U := by\n",
            "new": "    ptrB ((U ⊗ₖ (1 : Matrix κ κ ℂ)) * X * star (U ⊗ₖ (1 : Matrix κ κ ℂ))) = star U * ptrB X * U := by\n",
        }],
        "append": [], "expect": ["ptrB_local_conj"],
    },
    {
        "name": "AL1",
        "note": "面積律拿掉「割邊數」那個因子（熵 ≤ log D）。反例：兩條平行邊、D = 2，熵是 2 log 2",
        "edits": [{
            "file": "ErEpr/TensorNetwork.lean",
            "old": "    cutEntropy W (tnAmp ends T) ≤ (cutEdges ends W).card * Real.log D := by\n",
            "new": "    cutEntropy W (tnAmp ends T) ≤ Real.log D := by\n",
        }],
        "append": [{"file": "ErEpr/TensorNetwork.lean", "text":
            "/-- 演習 AL1：熵不受「log D」限制（兩條割邊、D = 2：已歸一，熵 2 log 2 > log 2）。 -/\n"
            "example : ¬ (cutEntropy ({0} : Finset (Fin 2)) (tnAmp (parEnds 2) (parTN 2 2 (parC 2 2))) ≤\n"
            "    Real.log 2) := by\n"
            "  rw [(area_law_saturated 2 2 (by norm_num)).2, card_cutEdges_par, not_le]\n"
            "  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)\n"
            "  push_cast\n"
            "  linarith\n\n"}],
        "expect": ["cutEntropy_tnAmp_le"],
    },
    {
        "name": "AL2",
        "note": "面積律拿掉歸一化（一般矩陣的反例見 Entropy 的 negctrl_unnormalized）",
        "edits": [{
            "file": "ErEpr/TensorNetwork.lean",
            "old": "    (hnorm : trace (cutMat W (tnAmp ends T) * (cutMat W (tnAmp ends T))ᴴ) = 1) :\n    cutEntropy W",
            "new": "    :\n    cutEntropy W",
        }],
        "append": [], "expect": ["cutEntropy_tnAmp_le"],
    },
]


def main(draft_path):
    drafts = json.load(open(draft_path, encoding="utf-8"))
    out = []
    for d in drafts:
        name = d["name"]
        e = {
            "name": name,
            "historical_evidence": d["evidence"],
            "historical_base": d["base"],
            "historical_red": d["historical_red"],
            "edits": [{"file": x["file"], "old": x["old"], "new": x["new"]} for x in d["edits"]],
            "append": d["append"],
            "expect": EXPECT[name],
        }
        if name in OVERRIDE:
            e.update(OVERRIDE[name])
        out.append(e)
    out = [EXTRA[0]] + out + EXTRA[1:]
    # 每筆 edit 在現行檔案裡必須剛好出現一次
    bad = []
    for e in out:
        for x in e["edits"]:
            n = (REPO / x["file"]).read_text(encoding="utf-8").count(x["old"])
            if n != 1:
                bad.append((e["name"], x["file"], n))
    if bad:
        sys.exit(f"edit 在現行檔案裡不是剛好一次：{bad}")
    p = REPO / "tools" / "drills_manifest.json"
    p.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"{p}：{len(out)} 份演習")


if __name__ == "__main__":
    main(sys.argv[1])
