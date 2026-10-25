import ErEpr.FirstLaw

/-!
# ErEpr.FirstLawGeneral：不對易的糾纏第一定律（影子的存在性）

參考態 `G = gibbs H β`（任何 Hermitian `H`、任何 `β`），擾動 `X` 是任何無跡 Hermitian 矩陣
（**不必**與 `G` 對易），路徑 `ρ(t) = G + t·X`（`gibbsPath`）。

* **影子存在**（`hasDerivAt_entropy_gibbsPath`）：`t ↦ S(ρ(t))` 在 0 **可微**，導數是 `β·tr(XH)`。
  不用固有值微擾。路線是夾擠：
  * 下界（Klein，`vnEntropy_le_beta_energy_add_log`）：`D(t) = β·tr(ρ(t)H) + log Z − S(ρ(t)) ≥ 0`；
  * 上界（`klein_gap_le_sq`）：`D(σ) ≤ tr((σ − G)²)/c`，`c` 是 Gibbs 機率的下界。由逐項
    `g(p, q) ≤ (p − q)²/q`（`kleinGap_le_sq`）與雙隨機恆等式
    `Σ_ij |W_ij|²(p_i − q_j)² = tr((σ − G)²)`（`trace_sub_gibbs_sq_eq_sum`）；
  * 沿路徑 `0 ≤ D(t) ≤ C·t²`，所以 `S(t) = S(0) + t·β·tr(XH) − D(t)` 在 0 可微。
  * 路徑在小 `t` 時仍是態（`eventually_gibbsPath_posSemidef`）：`G − c·1` 與 `c·1 + tX`
    都是么正共軛的實對角矩陣，前者半正定、後者在 `t` 夠小時半正定，相加就是 `ρ(t)`。
* **第二條路（互驗）**（`first_law_gibbs_of_hasDerivAt`）：只假設可微，用「`D ≥ 0`、`D(0) = 0`」的
  極小值論證得出同一個導數。
* **任何滿秩參考態**（`entanglement_first_law`）：`ρ₀ = U·diag(q)·Uᴴ`、`K = −log ρ₀`：
  `d/dt S(ρ₀ + tX)|₀ = tr(XK)`。
* **對易時退化回 `FirstLaw.lean`**（`first_law_general_agrees_diag`）：取 `ρ₀ = diag(q)`、`X = diag(v)`，
  一般公式的導數等於對易版直接微分得到的 `Σ v_i(−log q_i − 1)`（由導數唯一性，不是另算）。
* **負控制：影子不存在**（`negctrl_first_law_not_fullRank`）：參考態不滿秩時（`q = (1, 0)`），
  沿 `diag(1 − t/2, t/2)` 熵在 0 **不可微**（`−x log x` 在 0 的斜率發散）。滿秩不能拿掉。

範圍（引用前請讀）：
* 有限維、路徑是直線 `G + tX`；只有一階。
* 物理上這是「從糾纏推出重力」那條路的輸入之一；另一半（RT 公式、幾何動力學）本庫沒有，
  所以沒有任何關於 Einstein 方程的陳述。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real Topology

noncomputable section

/-! ## 逐項二次上界與雙隨機恆等式（純實數） -/

/-- `p ≥ 0`、`q > 0` ⇒ `g(p, q) ≤ (p − q)²/q`。 -/
theorem kleinGap_le_sq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : kleinGap p q ≤ (p - q) ^ 2 / q := by
  have hq0 : q ≠ 0 := hq.ne'
  rcases hp.eq_or_lt with rfl | hp
  · have h1 : kleinGap 0 q = q := by
      rw [kleinGap]
      ring
    have h2 : (0 - q) ^ 2 / q = q := by
      rw [zero_sub, neg_sq, sq, mul_div_assoc, div_self hq0, mul_one]
    linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hp hq)
    rw [Real.log_div hp.ne' hq0] at h
    have h2 := mul_le_mul_of_nonneg_left h hp.le
    rw [mul_sub] at h2
    have hid : p * (p / q - 1) - (p - q) = (p - q) ^ 2 / q := by
      field_simp
    rw [kleinGap]
    linarith

/-- 雙隨機恆等式：`Σ_ij M_ij (p_i − q_j)² = Σp² − 2Σ_ij p_i q_j M_ij + Σq²`。 -/
theorem sum_sq_doubly_stochastic {ι : Type*} [Fintype ι] (p q : ι → ℝ) (M : ι → ι → ℝ)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ∑ i, ∑ j, M i j * (p i - q j) ^ 2 =
      ∑ i, p i ^ 2 - 2 * ∑ i, ∑ j, p i * q j * M i j + ∑ j, q j ^ 2 := by
  have hA : ∑ i, ∑ j, M i j * p i ^ 2 = ∑ i, p i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hC : ∑ i, ∑ j, M i j * q j ^ 2 = ∑ j, q j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have hB : ∑ i, ∑ j, 2 * (p i * q j * M i j) = 2 * ∑ i, ∑ j, p i * q j * M i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hexp : ∀ i j, M i j * (p i - q j) ^ 2 =
      M i j * p i ^ 2 - 2 * (p i * q j * M i j) + M i j * q j ^ 2 := by
    intro i j
    ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC]

/-! ## 跡公式 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- `tr(σ²) = Σ p_i²`。 -/
theorem trace_mul_self_eq_sum {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) :
    trace (σ * σ) = ((∑ i, hσ.eigenvalues i ^ 2 : ℝ) : ℂ) := by
  conv_lhs => rw [eigU_spectral hσ]
  rw [conj_diag_mul_conj_diag _ (eigU_star_mul hσ), trace_mul_cycle, eigU_star_mul, Matrix.one_mul,
    trace_diagonal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- `tr(gibbs²) = Σ q_j²`。 -/
theorem trace_gibbs_mul_self_eq_sum (hH : H.IsHermitian) (β : ℝ) :
    trace (gibbs H β * gibbs H β) = ((∑ j, (bw hH β j / partZ hH β) ^ 2 : ℝ) : ℂ) := by
  rw [gibbs_eq_conj hH β, conj_diag_mul_conj_diag _ (eigU_star_mul hH), trace_mul_cycle,
    eigU_star_mul, Matrix.one_mul, trace_diagonal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- `tr(σ·gibbs) = Σ_ij p_i q_j |W_ij|²`，`W = Vᴴ U`。 -/
theorem trace_mul_gibbs_eq_sum {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) (hH : H.IsHermitian)
    (β : ℝ) :
    trace (σ * gibbs H β) = ((∑ i, ∑ j, hσ.eigenvalues i * (bw hH β j / partZ hH β) *
      Complex.normSq ((star (eigU hσ) * eigU hH) i j) : ℝ) : ℂ) := by
  rw [← trace_diag_mul_diag, star_mul, star_star, gibbs_eq_conj hH β]
  calc trace (σ * (eigU hH * diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) *
        star (eigU hH)))
      = trace (eigU hσ * diagonal (fun i => (hσ.eigenvalues i : ℂ)) * star (eigU hσ) *
          (eigU hH * diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) *
            star (eigU hH))) := by
        conv_lhs => rw [eigU_spectral hσ]
    _ = trace (diagonal (fun i => (hσ.eigenvalues i : ℂ)) * star (eigU hσ) *
          (eigU hH * diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) *
            star (eigU hH)) * eigU hσ) := by
        rw [Matrix.trace_mul_comm _ (eigU hσ)]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- `tr((σ − gibbs)²) = Σ_ij |W_ij|² (p_i − q_j)²`。 -/
theorem trace_sub_gibbs_sq_eq_sum {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) (hH : H.IsHermitian)
    (β : ℝ) :
    (trace ((σ - gibbs H β) * (σ - gibbs H β))).re =
      ∑ i, ∑ j, Complex.normSq ((star (eigU hσ) * eigU hH) i j) *
        (hσ.eigenvalues i - bw hH β j / partZ hH β) ^ 2 := by
  have hid := sum_sq_doubly_stochastic hσ.eigenvalues (fun j => bw hH β j / partZ hH β)
    (fun i j => Complex.normSq ((star (eigU hσ) * eigU hH) i j))
    (sum_normSq_row _ (eigU_cross_mul_star hσ hH)) (sum_normSq_col _ (eigU_cross_star_mul hσ hH))
  rw [sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub,
    Matrix.trace_mul_comm (gibbs H β) σ, trace_mul_self_eq_sum hσ, trace_mul_gibbs_eq_sum hσ hH β,
    trace_gibbs_mul_self_eq_sum hH β]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [hid]
  ring

/-! ## 二次上界 -/

/-- **二次上界**：`β·tr(σH) + log Z − S(σ) ≤ tr((σ − gibbs)²)/c`，`c` 是 Gibbs 機率的下界。 -/
theorem klein_gap_le_sq (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : trace σ = 1) {c : ℝ} (hc : 0 < c) (hcq : ∀ j, c ≤ bw hH β j / partZ hH β) :
    β * (trace (σ * H)).re + Real.log (partZ hH β) - vnEntropy σ ≤
      (trace ((σ - gibbs H β) * (σ - gibbs H β))).re / c := by
  have := nonempty_of_trace_eq_one htr
  have hZ := partZ_pos hH β
  rw [klein_gap_eq hH β hσ htr, trace_sub_gibbs_sq_eq_sum hσ.1 hH β, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  have hq : 0 < bw hH β j / partZ hH β := div_pos (Real.exp_pos _) hZ
  have h1 := kleinGap_le_sq (hσ.eigenvalues_nonneg i) hq
  have h2 : (hσ.1.eigenvalues i - bw hH β j / partZ hH β) ^ 2 / (bw hH β j / partZ hH β) ≤
      (hσ.1.eigenvalues i - bw hH β j / partZ hH β) ^ 2 / c :=
    div_le_div_of_nonneg_left (sq_nonneg _) hc (hcq j)
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (Complex.normSq_nonneg _)

/-- Gibbs 機率有正的下界。 -/
theorem exists_gibbs_lower [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    ∃ c, 0 < c ∧ ∀ j, c ≤ bw hH β j / partZ hH β := by
  have hZ := partZ_pos hH β
  refine ⟨Finset.univ.inf' Finset.univ_nonempty fun j => bw hH β j / partZ hH β, ?_,
    fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
  rw [Finset.lt_inf'_iff]
  exact fun j _ => div_pos (Real.exp_pos _) hZ

/-! ## 路徑 -/

/-- 路徑 `ρ(t) = gibbs H β + t·X`。 -/
def gibbsPath (H : Matrix ι ι ℂ) (β : ℝ) (X : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  gibbs H β + (t : ℂ) • X

theorem trace_gibbsPath [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) {X : Matrix ι ι ℂ}
    (hX0 : trace X = 0) (t : ℝ) : trace (gibbsPath H β X t) = 1 := by
  rw [gibbsPath, trace_add, trace_smul, hX0, smul_zero, add_zero, trace_gibbs hH β]

theorem gibbsPath_zero (H : Matrix ι ι ℂ) (β : ℝ) (X : Matrix ι ι ℂ) :
    gibbsPath H β X 0 = gibbs H β := by
  rw [gibbsPath, Complex.ofReal_zero, zero_smul, add_zero]

/-- 路徑上的能量是 `t` 的一次函數。 -/
theorem energy_gibbsPath (H : Matrix ι ι ℂ) (β : ℝ) (X : Matrix ι ι ℂ) (t : ℝ) :
    (trace (gibbsPath H β X t * H)).re =
      (trace (gibbs H β * H)).re + t * (trace (X * H)).re := by
  rw [gibbsPath, add_mul, trace_add, Matrix.smul_mul, trace_smul, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul]

/-- 路徑離起點的 `tr((ρ(t) − G)²) = t²·tr(X²)`。 -/
theorem sq_gibbsPath (H : Matrix ι ι ℂ) (β : ℝ) (X : Matrix ι ι ℂ) (t : ℝ) :
    (trace ((gibbsPath H β X t - gibbs H β) * (gibbsPath H β X t - gibbs H β))).re =
      t ^ 2 * (trace (X * X)).re := by
  rw [gibbsPath, add_sub_cancel_left, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul,
    smul_eq_mul, ← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]

/-- `gibbs − c·1` 半正定（`c` 不超過每個 Gibbs 機率）。 -/
theorem gibbs_sub_smul_one_posSemidef (hH : H.IsHermitian) (β : ℝ) {c : ℝ}
    (hcq : ∀ j, c ≤ bw hH β j / partZ hH β) : (gibbs H β - (c : ℂ) • 1).PosSemidef := by
  have hdiag : diagonal (fun j => ((bw hH β j / partZ hH β - c : ℝ) : ℂ)) =
      diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) - (c : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have h : eigU hH * diagonal (fun j => ((bw hH β j / partZ hH β - c : ℝ) : ℂ)) *
      star (eigU hH) = gibbs H β - (c : ℂ) • 1 := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      eigU_mul_star hH, ← gibbs_eq_conj hH β]
  rw [← h, star_eq_conjTranspose]
  exact (posSemidef_diagonal_iff.mpr fun j =>
    Complex.zero_le_real.mpr (sub_nonneg.mpr (hcq j))).mul_mul_conjTranspose_same _

/-- 小 `t` 時 `c·1 + t·X` 半正定（`c > 0`、`X` Hermitian）。 -/
theorem eventually_smul_one_add_posSemidef {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ (t : ℝ) in 𝓝 0, ((c : ℂ) • 1 + (t : ℂ) • X).PosSemidef := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, 0 < c + t * hX.eigenvalues j := by
    rw [Filter.eventually_all]
    intro j
    exact continuousAt_const.eventually_lt
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt (by simpa using hc)
  filter_upwards [hev] with t ht
  have hdiag : diagonal (fun j => ((c + t * hX.eigenvalues j : ℝ) : ℂ)) =
      (c : ℂ) • (1 : Matrix ι ι ℂ) + (t : ℂ) • diagonal (fun j => (hX.eigenvalues j : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have h : eigU hX * diagonal (fun j => ((c + t * hX.eigenvalues j : ℝ) : ℂ)) * star (eigU hX) =
      (c : ℂ) • 1 + (t : ℂ) • X := by
    rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      eigU_mul_star hX, Matrix.mul_smul, Matrix.smul_mul, ← eigU_spectral hX]
  rw [← h, star_eq_conjTranspose]
  exact (posSemidef_diagonal_iff.mpr fun j =>
    Complex.zero_le_real.mpr (ht j).le).mul_mul_conjTranspose_same _

/-- 小 `t` 時路徑仍是半正定矩陣。 -/
theorem eventually_gibbsPath_posSemidef [Nonempty ι] (hH : H.IsHermitian) (β : ℝ)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (gibbsPath H β X t).PosSemidef := by
  obtain ⟨c, hc, hcq⟩ := exists_gibbs_lower hH β
  filter_upwards [eventually_smul_one_add_posSemidef hX hc] with t ht
  have h : gibbsPath H β X t = (gibbs H β - (c : ℂ) • 1) + ((c : ℂ) • 1 + (t : ℂ) • X) := by
    rw [gibbsPath]
    abel
  rw [h]
  exact (gibbs_sub_smul_one_posSemidef hH β hcq).add ht

/-! ## 影子的存在性 -/

/-- **不對易的糾纏第一定律（Gibbs 參考態）**：`t ↦ S(gibbs + tX)` 在 0 可微，導數 `β·tr(XH)`。 -/
theorem hasDerivAt_entropy_gibbsPath [Nonempty ι] (hH : H.IsHermitian) (β : ℝ)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (hX0 : trace X = 0) :
    HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) (β * (trace (X * H)).re) 0 := by
  obtain ⟨c, hc, hcq⟩ := exists_gibbs_lower hH β
  have hG := vnEntropy_gibbs_eq_beta_energy_add_log hH β
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ),
      |vnEntropy (gibbsPath H β X t) - vnEntropy (gibbs H β) - t * (β * (trace (X * H)).re)| ≤
        (trace (X * X)).re / c * t ^ 2 := by
    filter_upwards [eventually_gibbsPath_posSemidef hH β hX] with t ht
    have htr := trace_gibbsPath hH β hX0 t
    have hlow := vnEntropy_le_beta_energy_add_log hH β ht htr
    have hup := klein_gap_le_sq hH β ht htr hc hcq
    rw [energy_gibbsPath] at hlow hup
    rw [sq_gibbsPath] at hup
    have hfrac : t ^ 2 * (trace (X * X)).re / c = (trace (X * X)).re / c * t ^ 2 := by ring
    rw [hfrac] at hup
    rw [abs_le]
    constructor <;> nlinarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => vnEntropy (gibbsPath H β X (0 + h)) - vnEntropy (gibbsPath H β X 0) -
      h • (β * (trace (X * H)).re)) =O[𝓝 0] fun h => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((trace (X * X)).re / c) ?_
    filter_upwards [hbound] with h hh
    rw [zero_add, gibbsPath_zero, smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg h)]
    exact hh
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- **第二條路（互驗）**：只假設可微，由「`D ≥ 0`、`D(0) = 0`」的極小值論證得出同一個導數。 -/
theorem first_law_gibbs_of_hasDerivAt [Nonempty ι] (hH : H.IsHermitian) (β : ℝ)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (hX0 : trace X = 0) {S' : ℝ}
    (hS : HasDerivAt (fun t => vnEntropy (gibbsPath H β X t)) S' 0) :
    S' = β * (trace (X * H)).re := by
  have hG := vnEntropy_gibbs_eq_beta_energy_add_log hH β
  have hlin : HasDerivAt (fun t : ℝ => β * ((trace (gibbs H β * H)).re + t * (trace (X * H)).re) +
      Real.log (partZ hH β)) (β * (trace (X * H)).re) 0 :=
    (((hasDerivAt_mul_const ((trace (X * H)).re)).const_add
      ((trace (gibbs H β * H)).re)).const_mul β).add_const _
  have hD : HasDerivAt (fun t : ℝ => β * ((trace (gibbs H β * H)).re + t * (trace (X * H)).re) +
      Real.log (partZ hH β) - vnEntropy (gibbsPath H β X t)) (β * (trace (X * H)).re - S') 0 :=
    hlin.sub hS
  have hmin : IsLocalMin (fun t : ℝ => β * ((trace (gibbs H β * H)).re + t * (trace (X * H)).re) +
      Real.log (partZ hH β) - vnEntropy (gibbsPath H β X t)) 0 := by
    filter_upwards [eventually_gibbsPath_posSemidef hH β hX] with t ht
    have h := vnEntropy_le_beta_energy_add_log hH β ht (trace_gibbsPath hH β hX0 t)
    rw [energy_gibbsPath] at h
    simp only [zero_mul, add_zero, gibbsPath_zero]
    linarith
  have := hmin.hasDerivAt_eq_zero hD
  linarith

/-! ## 任何滿秩參考態 -/

/-- **不對易的糾纏第一定律**：滿秩參考態 `ρ₀ = U·diag(q)·Uᴴ`、無跡 Hermitian 擾動 `X`：
`d/dt S(ρ₀ + tX)|₀ = tr(XK)`，`K = −log ρ₀`。 -/
theorem entanglement_first_law {ρ₀ : Matrix ι ι ℂ} (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ}
    (hρ : ρ₀ = (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ))
    (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (hX0 : trace X = 0) :
    HasDerivAt (fun t : ℝ => vnEntropy (ρ₀ + (t : ℂ) • X))
      (trace (X * modHamOf (U : Matrix ι ι ℂ) q)).re 0 := by
  have : Nonempty ι :=
    nonempty_of_trace_eq_one (σ := ρ₀) (by rw [hρ]; exact trace_unitary_conj_diag U hq1)
  have h := hasDerivAt_entropy_gibbsPath (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 hX hX0
  rw [one_mul] at h
  have hp : (fun t => vnEntropy (gibbsPath (modHamOf (U : Matrix ι ι ℂ) q) 1 X t)) =
      fun t : ℝ => vnEntropy (ρ₀ + (t : ℂ) • X) := by
    funext t
    rw [gibbsPath, gibbs_modHamOf U hq hq1, ← hρ]
  rw [hp] at h
  exact h

/-- **對易時退化回 `FirstLaw.lean`**：`ρ₀ = diag(q)`、`X = diag(v)` 時，一般公式的導數等於
對易版直接微分的 `Σ v_i(−log q_i − 1)`（由導數唯一性）。 -/
theorem first_law_general_agrees_diag {q : ι → ℝ} (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    {v : ι → ℝ} (hv : ∑ i, v i = 0) :
    (trace (diagonal (fun i => (v i : ℂ)) * modHamOf 1 q)).re =
      ∑ i, v i * (-Real.log (q i) - 1) := by
  have hρ : diagonal (fun i => (q i : ℂ)) =
      ((1 : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) *
        star ((1 : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) := by
    simp
  have hX : (diagonal fun i => (v i : ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hX0 : trace (diagonal fun i => (v i : ℂ)) = 0 := by
    rw [trace_diagonal, ← Complex.ofReal_sum, hv, Complex.ofReal_zero]
  have h1 := entanglement_first_law 1 hρ hq hq1 hX hX0
  have hpath : (fun t : ℝ => vnEntropy (diagonal (fun i => (q i : ℂ)) +
      (t : ℂ) • diagonal fun i => (v i : ℂ))) = fun t => vnEntropy (diagPath q v t) := by
    funext t
    congr 1
    rw [diagPath, ← diagonal_smul, diagonal_add]
    congr 1
    funext i
    simp
  rw [hpath] at h1
  exact h1.unique (hasDerivAt_entropy_diagPath hq v)

/-! ## 負控制：影子不存在 -/

/-- **負控制**：參考態不滿秩（`q = (1, 0)`）時，沿 `diag(1 − t/2, t/2)` 熵在 0 不可微。 -/
theorem negctrl_first_law_not_fullRank :
    ¬ DifferentiableAt ℝ (fun t => vnEntropy (diagPath ![1, 0] ![-1 / 2, 1 / 2] t)) 0 := by
  intro h
  have hS : (fun t => vnEntropy (diagPath ![1, 0] ![-1 / 2, 1 / 2] t)) =
      fun t => Real.negMulLog (1 + t * (-1 / 2)) + Real.negMulLog (0 + t * (1 / 2)) := by
    funext t
    rw [vnEntropy_diagPath, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hS] at h
  have h1 : DifferentiableAt ℝ (fun t : ℝ => Real.negMulLog (1 + t * (-1 / 2))) 0 := by
    have hin : DifferentiableAt ℝ (fun t : ℝ => 1 + t * (-1 / 2)) 0 := by fun_prop
    have hout : DifferentiableAt ℝ Real.negMulLog (1 + 0 * (-1 / 2)) :=
      Real.differentiableAt_negMulLog (by norm_num)
    exact hout.comp 0 hin
  have h2 : DifferentiableAt ℝ (fun t : ℝ => Real.negMulLog (0 + t * (1 / 2))) 0 := by
    have := h.sub h1
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    ring
  have h2' : DifferentiableAt ℝ (fun t : ℝ => Real.negMulLog (0 + t * (1 / 2))) (2 * 0) := by
    rwa [mul_zero]
  have h3 : DifferentiableAt ℝ Real.negMulLog 0 := by
    have hc := h2'.comp 0 (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => 2 * x) 0)
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    congr 1
    ring
  exact (Real.differentiableAt_negMulLog_iff.1 h3) rfl

end

end ErEpr
