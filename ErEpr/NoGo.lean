import ErEpr.Entropy

/-!
# ErEpr.NoGo：不可能定理——固定有限維系統的 Gibbs 熵，不能沿一段 β 區間等於 β²/16π

設 `H` 是有限維 Hermitian 矩陣，固有值 `E_i`，`w_i(β) = e^{-βE_i}`，
`Z = Σ w_i`、`N = Σ E_i w_i`、`Q = Σ E_i² w_i`。

* **閉式**（`vnEntropy_gibbs_eq_fn`）：`S(gibbs H β) = log Z + β·N/Z`。
  路線：`gibbs H β = U · diag(w/Z) · Uᴴ`（`gibbs_eq_conj`），熵在么正共軛下不變
  （`vnEntropy_unitary_conj`，由既有的 `vnEntropy_mul_comm`），對角矩陣的熵是 Shannon 熵。
* **導數**（`hasDerivAt_gibbsEntropyFn`）：`dS/dβ = -β · Var_β(H)`，
  `Var = Q/Z - (N/Z)²`。由 `Z' = -N`、`N' = -Q` 逐項求導得到。
* **變異數非負**（`energyVar_nonneg`）：`N² ≤ Q·Z`，Cauchy–Schwarz。
* **單調**（`antitoneOn_gibbsEntropyFn`）：`S` 在 `β ≥ 0` 上不增。
* **主定理**（`no_finite_dim_gibbs_matches_bh`）：對任何 `0 < a < b`，
  不可能對所有 `β ∈ (a, b)` 都有 `S(gibbs H β) = β²/16π`；
  一般形式是「任何在 `(a, b)` 上嚴格遞增的函數都不行」（`no_gibbs_entropy_strictMonoOn`）。
  以質量參數改寫（`β = 8πM`、`S = 4πM²`）是 `no_finite_dim_gibbs_matches_bh_mass`。
* **見證與健全性**：
  * `β = 0` 的 Gibbs 態是最大混合態，熵是 `log d`（`vnEntropy_gibbs_zero`），
    與閉式在 0 的值一致（`gibbsEntropyFn_zero`）；
  * 推論 `β ≥ 0` 時 `S ≤ log d`（`vnEntropy_gibbs_le_log_card`），
    與既有的 `vnEntropy_le_log_rank` 獨立走出的同一個上界一致（`vnEntropy_gibbs_le_log_card_of_rank`，對所有 β）；
  * `S ≥ 0`（`vnEntropy_gibbs_nonneg`）。
* **負控制：單點識別沒有內容**（`negctrl_single_point`）：
  維度 ≥ 2 時，總有某個 `β₀ > 0` 使 `S(gibbs H β₀) = β₀²/16π`（中間值定理）。
  所以主定理的內容全在「一整段區間」，不在任何單一點。

範圍（引用前請讀）：
* 物理讀法：`β²/16π` 是漸近平坦 Schwarzschild 黑洞以 `β = 8πM` 改寫的 Bekenstein–Hawking 熵
  `4πM²`，它隨 β 嚴格遞增（比熱為負）。本檔只對這種情形有內容；
  AdS 大黑洞的比熱為正、熵隨 β 遞減，**不適用**。
* 這**不是**對 ER=EPR 的反駁。它排除的是「黑洞 = 固定的有限維正則系綜」這一種識別法：
  剩下的可能是微正則系綜、隨質量變化的 Hilbert 空間，或無限維系統。
* 定理陳述只談矩陣與實函數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-! ## 定義：權重、配分函數與熵的閉式 -/

/-- Boltzmann 權重 `w_i(β) = e^{-βE_i}`，`E_i` 是 `H` 的固有值。 -/
def bw (hH : H.IsHermitian) (β : ℝ) (i : ι) : ℝ := Real.exp (-β * hH.eigenvalues i)

/-- 配分函數 `Z(β) = Σ_i e^{-βE_i}`。 -/
def partZ (hH : H.IsHermitian) (β : ℝ) : ℝ := ∑ i, bw hH β i

/-- `N(β) = Σ_i E_i e^{-βE_i}`；`N/Z` 是能量期望值。 -/
def partN (hH : H.IsHermitian) (β : ℝ) : ℝ := ∑ i, hH.eigenvalues i * bw hH β i

/-- `Q(β) = Σ_i E_i² e^{-βE_i}`；`Q/Z` 是能量平方的期望值。 -/
def partQ (hH : H.IsHermitian) (β : ℝ) : ℝ := ∑ i, hH.eigenvalues i ^ 2 * bw hH β i

/-- 能量變異數 `Var_β(H) = Q/Z - (N/Z)²`。 -/
def energyVar (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  partQ hH β / partZ hH β - (partN hH β / partZ hH β) ^ 2

/-- Gibbs 熵的閉式 `S(β) = log Z + β·N/Z`。 -/
def gibbsEntropyFn (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  Real.log (partZ hH β) + β * (partN hH β / partZ hH β)

theorem partZ_nonneg (hH : H.IsHermitian) (β : ℝ) : 0 ≤ partZ hH β :=
  Finset.sum_nonneg fun i _ => (Real.exp_pos (-β * hH.eigenvalues i)).le

theorem partZ_pos [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) : 0 < partZ hH β :=
  Finset.sum_pos (fun i _ => Real.exp_pos (-β * hH.eigenvalues i)) Finset.univ_nonempty

/-! ## B1：Gibbs 態在固有基底下 -/

/-- `tr e^{-βH} = Z(β)`。 -/
theorem trace_exp_neg_smul_eq (hH : H.IsHermitian) (β : ℝ) :
    trace (NormedSpace.exp (-(β : ℂ) • H)) = (partZ hH β : ℂ) := by
  rw [exp_neg_smul_eigen hH β, trace_mul_cycle, eigU_star_mul, Matrix.one_mul, trace_diagonal,
    partZ, Complex.ofReal_sum]
  rfl

/-- **B1**：`gibbs H β = U · diag(w_i/Z) · Uᴴ`。 -/
theorem gibbs_eq_conj (hH : H.IsHermitian) (β : ℝ) :
    gibbs H β =
      eigU hH * diagonal (fun i => ((bw hH β i / partZ hH β : ℝ) : ℂ)) * star (eigU hH) := by
  have hd : (fun i => ((bw hH β i / partZ hH β : ℝ) : ℂ)) =
      ((partZ hH β : ℂ))⁻¹ • fun i => ((bw hH β i : ℝ) : ℂ) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_div, div_eq_inv_mul]
  rw [hd, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul, gibbs, trace_exp_neg_smul_eq hH β,
    exp_neg_smul_eigen hH β]
  rfl

/-! ## B2–B3：熵 -/

/-- 么正共軛不改變熵（由 `vnEntropy_mul_comm`）。 -/
theorem vnEntropy_unitary_conj (U D : Matrix ι ι ℂ) (hU : star U * U = 1) :
    vnEntropy (U * D * star U) = vnEntropy D := by
  rw [vnEntropy_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **B2**：Gibbs 態的熵是 Boltzmann 分佈 `w_i/Z` 的 Shannon 熵。 -/
theorem vnEntropy_gibbs (hH : H.IsHermitian) (β : ℝ) :
    vnEntropy (gibbs H β) = ∑ i, Real.negMulLog (bw hH β i / partZ hH β) := by
  rw [gibbs_eq_conj hH β, vnEntropy_unitary_conj _ _ (eigU_star_mul hH),
    vnEntropy_diagonal (fun i => bw hH β i / partZ hH β)]

/-- **B3**：`S(gibbs H β) = log Z + β·N/Z`。 -/
theorem vnEntropy_gibbs_eq_fn [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    vnEntropy (gibbs H β) = gibbsEntropyFn hH β := by
  have hZ := partZ_pos hH β
  have key : ∀ i, Real.negMulLog (bw hH β i / partZ hH β) =
      β * (hH.eigenvalues i * bw hH β i) / partZ hH β +
        Real.log (partZ hH β) * (bw hH β i / partZ hH β) := by
    intro i
    rw [Real.negMulLog, bw, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    ring
  have h1 : ∑ i, bw hH β i / partZ hH β = 1 := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  rw [vnEntropy_gibbs hH β]
  simp only [key]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum, h1,
    gibbsEntropyFn, partN]
  ring

/-- `S ≥ 0`：每個 `w_i/Z` 都在 `[0, 1]`。 -/
theorem vnEntropy_gibbs_nonneg [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    0 ≤ vnEntropy (gibbs H β) := by
  have hZ := partZ_pos hH β
  rw [vnEntropy_gibbs hH β]
  refine Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg ?_ ?_
  · exact div_nonneg (Real.exp_pos _).le hZ.le
  · rw [div_le_one hZ]
    exact Finset.single_le_sum (f := fun j => bw hH β j)
      (fun j _ => (Real.exp_pos (-β * hH.eigenvalues j)).le) (Finset.mem_univ i)

/-! ## B4：導數 `dS/dβ = -β·Var` -/

theorem hasDerivAt_bw (hH : H.IsHermitian) (i : ι) (β : ℝ) :
    HasDerivAt (fun b => bw hH b i) (-hH.eigenvalues i * bw hH β i) β := by
  have h : HasDerivAt (fun b : ℝ => -b * hH.eigenvalues i) (-hH.eigenvalues i) β :=
    ((hasDerivAt_neg' (x := β)).mul_const (hH.eigenvalues i)).congr_deriv (neg_one_mul _)
  refine h.exp.congr_deriv ?_
  rw [bw]
  ring

/-- `Z' = -N`。 -/
theorem hasDerivAt_partZ (hH : H.IsHermitian) (β : ℝ) :
    HasDerivAt (partZ hH) (-partN hH β) β := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_bw hH i β
  refine h.congr_deriv ?_
  simp only [partN, neg_mul, Finset.sum_neg_distrib]

/-- `N' = -Q`。 -/
theorem hasDerivAt_partN (hH : H.IsHermitian) (β : ℝ) :
    HasDerivAt (partN hH) (-partQ hH β) β := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_bw hH i β).const_mul (hH.eigenvalues i)
  refine h.congr_deriv ?_
  rw [partQ, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **B4**：`dS/dβ = -β · Var_β(H)`。 -/
theorem hasDerivAt_gibbsEntropyFn [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    HasDerivAt (gibbsEntropyFn hH) (-β * energyVar hH β) β := by
  have hZ : partZ hH β ≠ 0 := (partZ_pos hH β).ne'
  have h := ((hasDerivAt_partZ hH β).log hZ).fun_add
    ((hasDerivAt_id' β).fun_mul ((hasDerivAt_partN hH β).fun_div (hasDerivAt_partZ hH β) hZ))
  refine h.congr_deriv ?_
  rw [energyVar]
  field_simp
  ring

/-! ## B5：變異數非負 -/

omit [DecidableEq ι] in
/-- 加權 Cauchy–Schwarz：`(Σ E_i w_i)² ≤ (Σ E_i² w_i)(Σ w_i)`，`w ≥ 0`。 -/
theorem sq_sum_le_mul_sum (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, E i * w i) ^ 2 ≤ (∑ i, E i ^ 2 * w i) * ∑ i, w i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => E i * Real.sqrt (w i))
    (fun i => Real.sqrt (w i))
  have e1 : ∀ i, E i * Real.sqrt (w i) * Real.sqrt (w i) = E i * w i := fun i => by
    rw [mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, (E i * Real.sqrt (w i)) ^ 2 = E i ^ 2 * w i := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have e3 : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  simp only [e1, e2, e3] at h
  exact h

/-- **B5**：`Var_β(H) ≥ 0`。 -/
theorem energyVar_nonneg [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) : 0 ≤ energyVar hH β := by
  have hZ := partZ_pos hH β
  have h : partN hH β ^ 2 ≤ partQ hH β * partZ hH β :=
    sq_sum_le_mul_sum (bw hH β) hH.eigenvalues fun i => (Real.exp_pos (-β * hH.eigenvalues i)).le
  rw [energyVar, sub_nonneg, div_pow, sq (partZ hH β), ← div_div,
    div_le_div_iff_of_pos_right hZ, div_le_iff₀ hZ]
  exact h

/-! ## B6：熵在 β ≥ 0 上不增 -/

/-- **B6**：`β ↦ S(gibbs H β)` 的閉式在 `[0, ∞)` 上不增。 -/
theorem antitoneOn_gibbsEntropyFn [Nonempty ι] (hH : H.IsHermitian) :
    AntitoneOn (gibbsEntropyFn hH) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact fun β _ => (hasDerivAt_gibbsEntropyFn hH β).continuousAt.continuousWithinAt
  · exact fun β _ => (hasDerivAt_gibbsEntropyFn hH β).differentiableAt.differentiableWithinAt
  · intro β hβ
    rw [interior_Ici] at hβ
    rw [(hasDerivAt_gibbsEntropyFn hH β).deriv]
    have h1 := mul_nonneg (Set.mem_Ioi.mp hβ).le (energyVar_nonneg hH β)
    linarith

/-! ## B7–B8：不可能定理 -/

/-- 一般形式：任何在 `(a, b)`（`0 ≤ a < b`）上嚴格遞增的函數，都不可能在整段區間上
等於某個固定有限維 `H` 的 Gibbs 熵。 -/
theorem no_gibbs_entropy_strictMonoOn [Nonempty ι] (hH : H.IsHermitian) {f : ℝ → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hf : StrictMonoOn f (Set.Ioo a b)) :
    ¬ ∀ β ∈ Set.Ioo a b, vnEntropy (gibbs H β) = f β := by
  intro h
  have h1 : (2 * a + b) / 3 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have h2 : (a + 2 * b) / 3 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have h12 : (2 * a + b) / 3 < (a + 2 * b) / 3 := by linarith
  have hanti := antitoneOn_gibbsEntropyFn hH
    (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ (2 * a + b) / 3))
    (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ (a + 2 * b) / 3)) h12.le
  rw [← vnEntropy_gibbs_eq_fn hH, ← vnEntropy_gibbs_eq_fn hH, h _ h1, h _ h2] at hanti
  exact absurd hanti (not_le.mpr (hf h1 h2 h12))

/-- **B7 不可能定理**：對任何有限維 Hermitian `H` 與任何 `0 < a < b`，
不可能對所有 `β ∈ (a, b)` 都有 `S(gibbs H β) = β²/16π`。

物理讀法（只在說明文字裡）：`β²/16π` 是漸近平坦 Schwarzschild 黑洞的 Bekenstein–Hawking 熵
（`S = 4πM²`、`β = 8πM`），隨 β 嚴格遞增，也就是比熱為負；而有限維 Gibbs 熵隨 β 不增。
限定：只對比熱為負的情形；AdS 大黑洞比熱為正，本定理不適用。
這不是對 ER=EPR 的反駁，是對「黑洞 = 固定有限維正則系綜」這種識別法的排除。
單一 β 點上的相等沒有內容（`negctrl_single_point`）。 -/
theorem no_finite_dim_gibbs_matches_bh [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ¬ ∀ β ∈ Set.Ioo a b, vnEntropy (gibbs H β) = β ^ 2 / (16 * π) := by
  refine no_gibbs_entropy_strictMonoOn (f := fun β => β ^ 2 / (16 * π)) hH ha.le hab
    fun x hx y _ hxy => ?_
  have hx0 : 0 < x := ha.trans hx.1
  have h16 : 0 < 16 * π := by positivity
  show x ^ 2 / (16 * π) < y ^ 2 / (16 * π)
  rw [div_lt_div_iff_of_pos_right h16]
  nlinarith

/-- **B8 以質量參數改寫**：不可能對所有 `M ∈ (a, b)` 都有 `S(gibbs H (8πM)) = 4πM²`。
（`8πM` 是 `hawking_beta` 的 β，`4πM²` 是 `first_law_area` 的 S；本條不依賴那兩條，
接上它們的耦合版在 `ErEpr/Chain.lean`。）
限定同 `no_finite_dim_gibbs_matches_bh`：只對比熱為負的漸近平坦 Schwarzschild；AdS 大黑洞不適用；
不是對 ER=EPR 的反駁，是對「黑洞 = 固定有限維正則系綜」這種識別法的排除。 -/
theorem no_finite_dim_gibbs_matches_bh_mass [Nonempty ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ¬ ∀ M ∈ Set.Ioo a b, vnEntropy (gibbs H (8 * π * M)) = 4 * π * M ^ 2 := by
  intro h
  have h8 : 0 < 8 * π := by positivity
  refine no_finite_dim_gibbs_matches_bh hH (mul_pos h8 ha) (mul_lt_mul_of_pos_left hab h8)
    fun β hβ => ?_
  have hM : β / (8 * π) ∈ Set.Ioo a b :=
    ⟨(lt_div_iff₀ h8).mpr (by linarith [hβ.1]), (div_lt_iff₀ h8).mpr (by linarith [hβ.2])⟩
  have hS := h _ hM
  rw [mul_div_cancel₀ β h8.ne'] at hS
  rw [hS, div_pow, eq_div_iff (by positivity)]
  field_simp
  ring

/-! ## B9：見證與交叉檢查 -/

/-- β = 0 的 Gibbs 態是最大混合態 `1/d`（對任何 `H`，不必 Hermitian）。 -/
theorem gibbs_zero (H : Matrix ι ι ℂ) :
    gibbs H 0 = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  rw [gibbs, Complex.ofReal_zero, neg_zero, zero_smul, NormedSpace.exp_zero, trace_one]
  push_cast
  rfl

/-- **B9**：β = 0 的熵是 `log d`（接既有的 `vnEntropy_maxMixed`）。 -/
theorem vnEntropy_gibbs_zero [Nonempty ι] (H : Matrix ι ι ℂ) :
    vnEntropy (gibbs H 0) = Real.log (Fintype.card ι) := by
  rw [gibbs_zero, vnEntropy_maxMixed]

/-- 閉式在 β = 0 的值也是 `log d`：與 `vnEntropy_gibbs_zero` 走不同的路，兩者一致。 -/
theorem gibbsEntropyFn_zero (hH : H.IsHermitian) :
    gibbsEntropyFn hH 0 = Real.log (Fintype.card ι) := by
  simp [gibbsEntropyFn, partZ, bw]

/-- **B9 推論**：`β ≥ 0` 時 `S(gibbs H β) ≤ log d`（由單調性 B6 與 β = 0 的值）。 -/
theorem vnEntropy_gibbs_le_log_card [Nonempty ι] (hH : H.IsHermitian) {β : ℝ} (hβ : 0 ≤ β) :
    vnEntropy (gibbs H β) ≤ Real.log (Fintype.card ι) := by
  rw [← vnEntropy_gibbs_zero H, vnEntropy_gibbs_eq_fn hH β, vnEntropy_gibbs_eq_fn hH 0]
  exact antitoneOn_gibbsEntropyFn hH (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hβ) hβ

/-- Gibbs 態半正定。 -/
theorem gibbs_posSemidef (hH : H.IsHermitian) (β : ℝ) : (gibbs H β).PosSemidef := by
  rw [gibbs_eq_conj hH β, star_eq_conjTranspose]
  refine (posSemidef_diagonal_iff.mpr fun i => ?_).mul_mul_conjTranspose_same _
  exact Complex.zero_le_real.mpr (div_nonneg (Real.exp_pos _).le (partZ_nonneg hH β))

/-- Gibbs 態的跡是 1。 -/
theorem trace_gibbs [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) : trace (gibbs H β) = 1 := by
  rw [gibbs, trace_smul, smul_eq_mul, inv_mul_cancel₀ (trace_exp_neg_smul_ne_zero hH β)]

/-- **交叉檢查**：由既有的 `vnEntropy_le_log_rank`（Jensen，不經導數）獨立得到
`S(gibbs H β) ≤ log d`，對**所有** β 都成立；與 `vnEntropy_gibbs_le_log_card` 一致。 -/
theorem vnEntropy_gibbs_le_log_card_of_rank [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    vnEntropy (gibbs H β) ≤ Real.log (Fintype.card ι) :=
  vnEntropy_le_log_of_rank_le (gibbs_posSemidef hH β) (trace_gibbs hH β) (rank_le_card_width _)

/-! ## B10：負控制——單點識別沒有內容 -/

/-- **負控制（單點）**：維度 ≥ 2 時，總有某個 `β₀ > 0` 使 `S(gibbs H β₀) = β₀²/16π`。
證法：`g(β) = S(β) - β²/16π` 連續，`g(0) = log d > 0`，
`g(8(1 + log d)) ≤ log d - 4(1 + log d)²/π < 0`，中間值定理。
所以「黑洞熵 = Gibbs 熵」在單一 β 點上永遠調得到，沒有內容；不可能定理的內容在整段區間。 -/
theorem negctrl_single_point [Nonempty ι] (hH : H.IsHermitian) (hcard : 1 < Fintype.card ι) :
    ∃ β₀ > 0, vnEntropy (gibbs H β₀) = β₀ ^ 2 / (16 * π) := by
  have hL0 : 0 < Real.log (Fintype.card ι) := Real.log_pos (by exact_mod_cast hcard)
  have hπ : 0 < 16 * π := by positivity
  have hcont : Continuous (gibbsEntropyFn hH) :=
    continuous_iff_continuousAt.mpr fun β => (hasDerivAt_gibbsEntropyFn hH β).continuousAt
  have hB0 : (0 : ℝ) ≤ 8 * (1 + Real.log (Fintype.card ι)) := by linarith
  have hgc : ContinuousOn (fun β => gibbsEntropyFn hH β - β ^ 2 / (16 * π))
      (Set.Icc 0 (8 * (1 + Real.log (Fintype.card ι)))) :=
    (hcont.sub ((continuous_pow 2).div_const _)).continuousOn
  have hgB : gibbsEntropyFn hH (8 * (1 + Real.log (Fintype.card ι))) -
      (8 * (1 + Real.log (Fintype.card ι))) ^ 2 / (16 * π) ≤ 0 := by
    have h1 := vnEntropy_gibbs_le_log_card hH hB0
    rw [vnEntropy_gibbs_eq_fn hH] at h1
    have h2 : Real.log (Fintype.card ι) ≤ (8 * (1 + Real.log (Fintype.card ι))) ^ 2 / (16 * π) := by
      rw [le_div_iff₀ hπ]
      nlinarith [mul_le_mul_of_nonneg_left Real.pi_le_four hL0.le,
        sq_nonneg (Real.log (Fintype.card ι))]
    linarith
  have hg0 : 0 ≤ gibbsEntropyFn hH 0 - (0 : ℝ) ^ 2 / (16 * π) := by
    rw [gibbsEntropyFn_zero hH, zero_pow two_ne_zero, zero_div, sub_zero]
    exact hL0.le
  obtain ⟨β₀, ⟨hβ0, -⟩, hβ₀⟩ := intermediate_value_Icc' hB0 hgc ⟨hgB, hg0⟩
  have hval : vnEntropy (gibbs H β₀) = β₀ ^ 2 / (16 * π) := by
    rw [vnEntropy_gibbs_eq_fn hH]
    exact sub_eq_zero.mp hβ₀
  refine ⟨β₀, lt_of_le_of_ne hβ0 fun h => ?_, hval⟩
  rw [← h, vnEntropy_gibbs_zero H, zero_pow two_ne_zero, zero_div] at hval
  linarith

/-- 負控制的具體實例：`H = diag(0, 1)`。 -/
theorem negctrl_single_point_H2 :
    ∃ β₀ > 0, vnEntropy (gibbs H2 β₀) = β₀ ^ 2 / (16 * π) :=
  negctrl_single_point H2_isHermitian (by simp)

/-! ## S5（便宜半段）：β 是熵對能量的斜率 -/

/-- 能量期望值 `E(β) = N/Z`（保真見 `trace_gibbs_mul_self`：它就是 `tr(gibbs · H)`）。 -/
def energyMean (hH : H.IsHermitian) (β : ℝ) : ℝ := partN hH β / partZ hH β

/-- **保真**：`tr(gibbs H β · H) = E(β)`。 -/
theorem trace_gibbs_mul_self (hH : H.IsHermitian) (β : ℝ) :
    trace (gibbs H β * H) = ((energyMean hH β : ℝ) : ℂ) := by
  conv_lhs => rw [gibbs_eq_conj hH β]
  conv_lhs => arg 1; arg 2; rw [eigU_spectral hH]
  rw [conj_diag_mul_conj_diag _ (eigU_star_mul hH), trace_mul_cycle, eigU_star_mul,
    Matrix.one_mul, trace_diagonal, energyMean, partN, Finset.sum_div]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `dE/dβ = −Var_β(H)`。 -/
theorem hasDerivAt_energyMean [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    HasDerivAt (energyMean hH) (-energyVar hH β) β := by
  have hZ : partZ hH β ≠ 0 := (partZ_pos hH β).ne'
  refine ((hasDerivAt_partN hH β).fun_div (hasDerivAt_partZ hH β) hZ).congr_deriv ?_
  rw [energyVar]
  field_simp
  ring

/-- **S5**：`dS/dβ = β · dE/dβ`。EPR 側的 β 就是熵對能量的斜率（在 `dE/dβ ≠ 0` 處 `dS/dE = β`）。
`first_law_area` 在 ER 側把同一條關係 `dS/dM = β(M)` 當**假設** `hS`；這裡在 EPR 側是**定理**。
所以溫度那一行兩側用的是同一個定義：熵對能量的斜率（CHAIN_DESIGN §11）。
限定：只是同一個定義，不是同一個數值；兩側的 β 相等仍是識別假設 h 的一部分。 -/
theorem gibbs_dS_eq_beta_dE [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    deriv (gibbsEntropyFn hH) β = β * deriv (energyMean hH) β := by
  rw [(hasDerivAt_gibbsEntropyFn hH β).deriv, (hasDerivAt_energyMean hH β).deriv]
  ring

/-- 斜率形式：`dE/dβ ≠ 0`（例如 `H` 不是純量）時 `(dS/dβ)/(dE/dβ) = β`。 -/
theorem gibbs_entropy_energy_slope [Nonempty ι] (hH : H.IsHermitian) (β : ℝ)
    (hvar : energyVar hH β ≠ 0) :
    deriv (gibbsEntropyFn hH) β / deriv (energyMean hH) β = β := by
  rw [gibbs_dS_eq_beta_dE, (hasDerivAt_energyMean hH β).deriv]
  field_simp

/-! ## 負控制：H 隨 β 變就對得上

不可能定理的內容全在「H 固定」。允許 H 隨溫度改變時，同一個維度就夠讓每個 β 都恰好對上
`β²/16π`：任何滿秩分佈都是某個 H 的 Gibbs 態（取 `H = diag(−log p / β)`，即 T-c 的模哈密頓量
除以 β），再用中間值定理挑出熵恰好的分佈。 -/

/-- 兩段分佈 `(1 − q, q/(n+1), …, q/(n+1))`，共 `n + 2` 個。 -/
def twoTierDist (n : ℕ) (q : ℝ) (i : Fin (n + 2)) : ℝ := if i = 0 then 1 - q else q / (n + 1)

theorem sum_twoTierDist (n : ℕ) (q : ℝ) : ∑ i, twoTierDist n q i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [twoTierDist, Fin.succ_ne_zero, if_true, if_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sum_negMulLog_twoTierDist (n : ℕ) (q : ℝ) :
    ∑ i, Real.negMulLog (twoTierDist n q i) =
      Real.negMulLog (1 - q) + (n + 1) * Real.negMulLog (q / (n + 1)) := by
  rw [Fin.sum_univ_succ]
  simp only [twoTierDist, Fin.succ_ne_zero, if_true, if_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- 兩段分佈的熵在 `0` 與 `log (n + 2)` 之間連續變動，所以每個中間值都取得到。 -/
theorem exists_twoTier_entropy (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs : s < Real.log (n + 2)) :
    ∃ q ∈ Set.Ioo (0 : ℝ) ((n + 1) / (n + 2)),
      Real.negMulLog (1 - q) + (n + 1) * Real.negMulLog (q / (n + 1)) = s := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hcont : ContinuousOn (fun q : ℝ => Real.negMulLog (1 - q) + (n + 1) * Real.negMulLog (q / (n + 1)))
      (Set.Icc 0 ((n + 1) / (n + 2))) := by
    apply Continuous.continuousOn
    fun_prop
  have h0 : Real.negMulLog (1 - 0) + (n + 1) * Real.negMulLog (0 / (n + 1)) = 0 := by simp
  have e1 : 1 - ((n : ℝ) + 1) / (n + 2) = 1 / (n + 2) := by
    field_simp
    ring
  have e2 : ((n : ℝ) + 1) / (n + 2) / (n + 1) = 1 / (n + 2) := by
    field_simp
  have h1 : Real.negMulLog (1 - (n + 1) / (n + 2)) + (n + 1) * Real.negMulLog ((n + 1) / (n + 2) / (n + 1)) =
      Real.log (n + 2) := by
    rw [e1, e2, Real.negMulLog, one_div, Real.log_inv]
    field_simp
    ring
  have hle : (0 : ℝ) ≤ (n + 1) / (n + 2) := by positivity
  obtain ⟨q, hq, hqs⟩ := intermediate_value_Ioo hle hcont (by rw [h0, h1]; exact ⟨hs0, hs⟩)
  exact ⟨q, hq, hqs⟩

/-- 任何 `0 < s < log (n + 2)`、任何 `β ≠ 0`：存在 `n + 2` 維的 Hermitian `H`，`S(gibbs H β) = s`。 -/
theorem exists_hamiltonian_gibbs_entropy_eq (n : ℕ) {β : ℝ} (hβ : β ≠ 0) {s : ℝ} (hs0 : 0 < s)
    (hs : s < Real.log (n + 2)) :
    ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, H.IsHermitian ∧ vnEntropy (gibbs H β) = s := by
  obtain ⟨q, ⟨hq0, hq1⟩, hqs⟩ := exists_twoTier_entropy n hs0 hs
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hq1' : q < 1 := hq1.trans ((div_lt_one (by positivity)).mpr (by linarith))
  have hp : ∀ i, 0 < twoTierDist n q i := by
    intro i
    unfold twoTierDist
    split_ifs
    · linarith
    · positivity
  refine ⟨diagonal fun i => ((-Real.log (twoTierDist n q i) / β : ℝ) : ℂ), ?_, ?_⟩
  · rw [Matrix.IsHermitian, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  · have he : ∀ i, Real.exp (-β * (-Real.log (twoTierDist n q i) / β)) = twoTierDist n q i := by
      intro i
      rw [show -β * (-Real.log (twoTierDist n q i) / β) = Real.log (twoTierDist n q i) by
        field_simp]
      exact Real.exp_log (hp i)
    rw [gibbs_diagonal_real]
    simp only [he, sum_twoTierDist, div_one]
    rw [vnEntropy_diagonal, sum_negMulLog_twoTierDist]
    exact hqs

/-- **負控制**：H 隨 β 變就對得上。對任何 `0 < a < b`，有一個維度 `n + 2`，使每個 `β ∈ (a, b)` 都有
`n + 2` 維的 Hermitian `H_β` 滿足 `S(gibbs H_β β) = β²/16π`。 -/
theorem negctrl_nogo_varying_hamiltonian {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ n : ℕ, ∀ β ∈ Set.Ioo a b, ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
      H.IsHermitian ∧ vnEntropy (gibbs H β) = β ^ 2 / (16 * π) := by
  refine ⟨⌈Real.exp (b ^ 2 / (16 * π))⌉₊, fun β hβ => ?_⟩
  have hβ0 : 0 < β := ha.trans hβ.1
  have hπ : 0 < 16 * π := by positivity
  refine exists_hamiltonian_gibbs_entropy_eq _ hβ0.ne' (by positivity) ?_
  have h1 : β ^ 2 / (16 * π) < b ^ 2 / (16 * π) :=
    div_lt_div_of_pos_right (by nlinarith [hβ.2]) hπ
  have h2 : b ^ 2 / (16 * π) < Real.log ((⌈Real.exp (b ^ 2 / (16 * π))⌉₊ : ℕ) + 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have := Nat.le_ceil (Real.exp (b ^ 2 / (16 * π)))
    linarith
  linarith

/-- **不可能定理的內容全在「H 固定」**：同一個維度、同一段溫度區間，
* 任何**固定**的 H 都做不到（`no_finite_dim_gibbs_matches_bh`）；
* 每個 β **換一個** H 就做得到（`negctrl_nogo_varying_hamiltonian`）。
差別只在量詞的順序：`∃ H, ∀ β` 為假，`∀ β, ∃ H` 為真。 -/
theorem nogo_hinges_on_fixed_hamiltonian {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ n : ℕ,
      (∀ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ, H.IsHermitian →
        ¬ ∀ β ∈ Set.Ioo a b, vnEntropy (gibbs H β) = β ^ 2 / (16 * π)) ∧
      (∀ β ∈ Set.Ioo a b, ∃ H : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ,
        H.IsHermitian ∧ vnEntropy (gibbs H β) = β ^ 2 / (16 * π)) := by
  obtain ⟨n, hn⟩ := negctrl_nogo_varying_hamiltonian ha hab
  exact ⟨n, fun H hH => no_finite_dim_gibbs_matches_bh hH ha hab, hn⟩

end

end ErEpr
