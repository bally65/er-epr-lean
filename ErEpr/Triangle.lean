import ErEpr.Klein
import ErEpr.Charts

/-!
# ErEpr.Triangle：物質、能量、信息三角的三塊便宜磚（`docs/TRIANGLE.md` §5 的 T-a、T-b、T-e）

自然單位 `G = c = ħ = k_B = 1`，熵以 nat 計（一個位元是 `ln 2`）。

* **T-a 黑洞填滿 Bekenstein 界**（`bekensteinBound_throat`、`first_law_saturates_bekenstein`）：
  Bekenstein 界的右邊是 `2πRE`（`bekensteinBound`）。取喉部（視界）的面積半徑
  `R = r(M/2) = 2M`（`rOfRho_throat`）、能量 `E = M`，則 `2πRE = A/4`；
  滿足 `first_law_area` 假設的熵函數在 `M` 處恰好等於這個界。
  負控制 `negctrl_bekenstein_isotropic_radius`：若誤用各向同性座標 `ρ = M/2` 當半徑，只得 `A/16`。
* **T-b 熱庫那一半的 Landauer**（`reservoir_entropy_le_beta_heat`）：熱庫從 `gibbs H β` 變到任何
  態 `ρ`，熵的增加不超過 `β` 乘吸收的能量；等號只在 `ρ` 仍是同溫的 Gibbs 態
  （`reservoir_entropy_eq_beta_heat_iff`）。推論 `landauer_reservoir_bit`：熱庫的熵至少增加
  `ln 2`（吸收一個位元）時，它至少吸收 `ln 2 / β = T ln 2` 的能量。
  負控制 `negctrl_reservoir_not_gibbs`：熱庫的起點不是同溫 Gibbs 態時，這個不等式可以失敗。
* **T-e 黑洞打平 Landauer**（`hasDerivAt_bh_energy_of_entropy`、`bh_landauer_saturated`）：
  沿 `S = 4πM²`，能量作為熵的函數 `E(S) = √(S/4π)` 的導數是 `1/(8πM)`；
  `β` 滿足單位錐角條件時這就是 `1/β = T`。所以熵增加 `ln 2` 時能量在一階上恰好增加
  `T ln 2`：Landauer 的下限被取到。

範圍（引用前請讀）：
* T-a 只是代數恆等式：「R 取視界的面積半徑」是約定，`S = 4πM²` 繼承 `first_law_area` 的假設
  （第一定律、`E = M`、單位錐角條件）。它**不**經過 Klein 不等式（`Coupling.lean` 有斷言）。
* T-b 是完整 Landauer 的熱庫那一半；完整版（系統與熱庫聯合么正演化，加上熵的次可加性）
  在 `ErEpr/Landauer.lean`（`docs/TRIANGLE.md` 的 T-d）。
* T-e 是一階（導數）陳述，同樣繼承 `first_law_area` 的假設。
* 本檔不證 Bekenstein 界本身，也不證 Landauer 原理本身。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real

noncomputable section

/-! ## T-a：黑洞填滿 Bekenstein 界 -/

/-- Bekenstein 界的右邊 `2πRE`（自然單位，熵以 nat 計）。 -/
def bekensteinBound (R E : ℝ) : ℝ := 2 * π * R * E

/-- **T-a**：喉部的面積半徑 `R = r(M/2) = 2M`、能量 `E = M` 時，`2πRE = A/4`。 -/
theorem bekensteinBound_throat {M : ℝ} (hM : 0 < M) :
    bekensteinBound (rOfRho M (M / 2)) M = areaIso M (M / 2) / 4 := by
  rw [bekensteinBound, rOfRho_throat hM.ne', throat_area_eq hM]
  ring

/-- 接上第一定律：滿足 `first_law_area` 假設的熵函數，在 `M` 處恰好等於 Bekenstein 界。 -/
theorem first_law_saturates_bekenstein {S β : ℝ → ℝ} (h0 : S 0 = 0)
    (hS : ∀ m, HasDerivAt S (β m) m) (hβ : ∀ m, 0 < m → UnitConeAngle m (β m)) {M : ℝ}
    (hM : 0 < M) :
    S M = bekensteinBound (rOfRho M (M / 2)) M := by
  rw [bekensteinBound_throat hM]
  exact (first_law_area h0 hS hβ hM).2

/-- **負控制**：誤用各向同性座標 `ρ = M/2` 當半徑，界只有 `A/16`，不等於 `A/4`。 -/
theorem negctrl_bekenstein_isotropic_radius {M : ℝ} (hM : 0 < M) :
    bekensteinBound (M / 2) M ≠ areaIso M (M / 2) / 4 := by
  rw [bekensteinBound, throat_area_eq hM]
  intro h
  have hp : 0 < π * M ^ 2 := mul_pos Real.pi_pos (pow_pos hM 2)
  linarith

/-! ## T-b：熱庫那一半的 Landauer -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- **T-b**：熱庫從 `gibbs H β` 變到任何態 `ρ`，`ΔS ≤ β·ΔE`。 -/
theorem reservoir_entropy_le_beta_heat (hH : H.IsHermitian) (β : ℝ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy ρ - vnEntropy (gibbs H β) ≤
      β * ((trace (ρ * H)).re - (trace (gibbs H β * H)).re) := by
  have := nonempty_of_trace_eq_one htr
  have h1 := vnEntropy_le_beta_energy_add_log hH β hρ htr
  rw [vnEntropy_gibbs_eq_beta_energy_add_log hH β]
  linarith

/-- 等號只在終態仍是同溫的 Gibbs 態（準靜態）。 -/
theorem reservoir_entropy_eq_beta_heat_iff (hH : H.IsHermitian) (β : ℝ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy ρ - vnEntropy (gibbs H β) =
        β * ((trace (ρ * H)).re - (trace (gibbs H β * H)).re) ↔ ρ = gibbs H β := by
  have := nonempty_of_trace_eq_one htr
  rw [← vnEntropy_eq_beta_energy_add_log_iff hH β hρ htr,
    vnEntropy_gibbs_eq_beta_energy_add_log hH β]
  constructor <;> intro h <;> linarith

/-- **一個位元**：`β > 0` 時，熱庫的熵至少增加 `ln 2`，它吸收的能量至少是 `ln 2 / β`。 -/
theorem landauer_reservoir_bit (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hbit : Real.log 2 ≤ vnEntropy ρ - vnEntropy (gibbs H β)) :
    Real.log 2 / β ≤ (trace (ρ * H)).re - (trace (gibbs H β * H)).re := by
  rw [div_le_iff₀ hβ]
  have := reservoir_entropy_le_beta_heat hH β hρ htr
  linarith

/-- **負控制**：熱庫的起點不是同溫 Gibbs 態時，`ΔS ≤ β·ΔE` 可以失敗。
`H = diag(0, 1)`、`β = ln 2`；起點取 `β′ = −ln 2` 的 Gibbs 態 `diag(1/3, 2/3)`，
終點取 `β = ln 2` 的 Gibbs 態 `diag(2/3, 1/3)`：熵不變，能量卻減少 `1/3`。 -/
theorem negctrl_reservoir_not_gibbs :
    ¬ (vnEntropy (gibbs H2 (Real.log 2)) - vnEntropy (gibbs H2 (-Real.log 2)) ≤
        Real.log 2 * ((trace (gibbs H2 (Real.log 2) * H2)).re -
          (trace (gibbs H2 (-Real.log 2) * H2)).re)) := by
  have hS : vnEntropy (gibbs H2 (Real.log 2)) = vnEntropy (gibbs H2 (-Real.log 2)) := by
    rw [gibbs_H2_log2, gibbs_H2_neg_log2, vnEntropy_diagonal, vnEntropy_diagonal]
    simp [Fin.sum_univ_two, add_comm]
  have hE1 : (trace (gibbs H2 (Real.log 2) * H2)).re = 1 / 3 := by
    rw [gibbs_H2_log2]
    norm_num [H2, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
  have hE2 : (trace (gibbs H2 (-Real.log 2) * H2)).re = 2 / 3 := by
    rw [gibbs_H2_neg_log2]
    norm_num [H2, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]
  rw [hS, hE1, hE2, sub_self, not_le]
  linarith [Real.log_pos one_lt_two]

/-! ## T-e：黑洞打平 Landauer -/

/-- `S = 4πM²` 反解：`M = √(S/4π)`。 -/
theorem bh_energy_of_entropy {M : ℝ} (hM : 0 ≤ M) :
    Real.sqrt (4 * π * M ^ 2 / (4 * π)) = M := by
  rw [mul_div_cancel_left₀ _ (mul_pos (by norm_num) Real.pi_pos).ne', Real.sqrt_sq hM]

/-- **T-e**：沿 `S = 4πM²`，`dE/dS = 1/(8πM)`。 -/
theorem hasDerivAt_bh_energy_of_entropy {M : ℝ} (hM : 0 < M) :
    HasDerivAt (fun s => Real.sqrt (s / (4 * π))) (1 / (8 * π * M)) (4 * π * M ^ 2) := by
  have hf : HasDerivAt (fun s : ℝ => s / (4 * π)) (1 / (4 * π)) (4 * π * M ^ 2) :=
    (hasDerivAt_id' (x := 4 * π * M ^ 2)).div_const _
  have hx : 4 * π * M ^ 2 / (4 * π) ≠ 0 :=
    (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hM 2))
      (mul_pos (by norm_num) Real.pi_pos)).ne'
  refine (hf.sqrt hx).congr_deriv ?_
  show 1 / (4 * π) / (2 * Real.sqrt (4 * π * M ^ 2 / (4 * π))) = 1 / (8 * π * M)
  rw [bh_energy_of_entropy hM.le, div_div,
    div_eq_div_iff (mul_pos (mul_pos (by norm_num) Real.pi_pos) (mul_pos (by norm_num) hM)).ne'
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) hM).ne']
  ring

/-- 接上 ER-3：`β` 滿足單位錐角條件時，`dE/dS = 1/β = T`：熵增加 `ln 2`，
能量在一階上恰好增加 `T ln 2`。 -/
theorem bh_landauer_saturated {M β : ℝ} (hM : 0 < M) (hβ : UnitConeAngle M β) :
    HasDerivAt (fun s => Real.sqrt (s / (4 * π))) (1 / β) (4 * π * M ^ 2) := by
  rw [(hawking_beta hM).mp hβ]
  exact hasDerivAt_bh_energy_of_entropy hM

end

end ErEpr
