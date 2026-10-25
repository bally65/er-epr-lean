import ErEpr.NoGo

/-!
# ErEpr.Klein：Gibbs 變分原理（CHAIN_DESIGN §5.2 的 S5，Klein 那一半）

設 `H` 是有限維 Hermitian 矩陣，`Z = Σ e^{-βE_j}`（`partZ`）。對任何密度矩陣 `σ`
（半正定、跡為 1）：

* **Klein 不等式**（`vnEntropy_le_beta_energy_add_log`）：`S(σ) ≤ β·tr(σH) + log Z`；
* **等號只在 Gibbs 態**（`vnEntropy_eq_beta_energy_add_log_iff`）：取等號 ⇔ `σ = gibbs H β`；
* Gibbs 態本身取等號（`vnEntropy_gibbs_eq_beta_energy_add_log`），也就是
  `S(gibbs) = β·tr(gibbs·H) + log Z`；
* **最大熵**（`vnEntropy_le_gibbs_of_energy_eq`、`vnEntropy_lt_gibbs_of_energy_eq`）：
  能量期望值與 Gibbs 態相同的所有態裡，Gibbs 態的熵最大，而且是唯一的最大者。

路線（不需要矩陣對數，也不需要 Jensen）：
* `σ = V·diag(p)·Vᴴ`、`H = U·diag(E)·Uᴴ`，`W = Vᴴ U` 是么正矩陣，`M_ij = |W_ij|²` 是雙隨機矩陣
  （`sum_normSq_row`、`sum_normSq_col`）；
* `tr(σH) = Σ_ij p_i M_ij E_j`（`trace_mul_eq_sum`）；
* 以 `q_j = e^{-βE_j}/Z` 記 Gibbs 機率，右邊減左邊恰好等於
  `Σ_ij M_ij · g(p_i, q_j)`，其中 `g(p, q) = p log p − p log q − (p − q)`（`klein_gap_eq`）；
* `g ≥ 0`，且 `p ≠ q` 時 `g > 0`（`kleinGap_nonneg`、`kleinGap_pos`，由 `log x ≤ x − 1`）。
* 等號 ⇒ 凡 `W_ij ≠ 0` 就有 `p_i = q_j` ⇒ `diag(p)·W = W·diag(q)` ⇒ `σ = U·diag(q)·Uᴴ = gibbs H β`。

見證：`H = diag(0, 1)`、`β = ln 2` 時，純態 `|0⟩⟨0|`（`negctrl_klein_pure_H2`）與另一個溫度的
Gibbs 態（`negctrl_klein_other_beta_H2`）都**嚴格**小於右邊。

範圍（引用前請讀）：
* 這是有限維、固定 `H` 的陳述。物理讀法：在能量固定時 Gibbs 態熵最大；`β > 0` 時等價於
  自由能 `tr(σH) − S/β` 在 Gibbs 態取極小。它也是 Landauer 與（Casini 形式的）Bekenstein
  兩種界共同的數學核心「相對熵 ≥ 0」在 Gibbs 參考態上的特例；那兩種界本身**沒有**在本檔證明。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real

noncomputable section

/-! ## 逐項不等式與雙隨機恆等式（純實數） -/

/-- 逐項的缺口 `g(p, q) = p log p − p log q − (p − q)`。 -/
def kleinGap (p q : ℝ) : ℝ := p * Real.log p - p * Real.log q - (p - q)

/-- `p ≥ 0`、`q > 0` ⇒ `g(p, q) ≥ 0`（由 `log x ≤ x − 1`，`x = q/p`）。 -/
theorem kleinGap_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : 0 ≤ kleinGap p q := by
  rcases hp.eq_or_lt with rfl | hp
  · have h : kleinGap 0 q = q := by
      rw [kleinGap]
      ring
    rw [h]
    exact hq.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hp.le
    have h3 : p * (q / p - 1) = q - p := by rw [mul_sub, mul_one, mul_div_cancel₀ q hp.ne']
    rw [h3, mul_sub] at h2
    rw [kleinGap]
    linarith

/-- `p ≥ 0`、`q > 0`、`p ≠ q` ⇒ `g(p, q) > 0`。 -/
theorem kleinGap_pos {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≠ q) : 0 < kleinGap p q := by
  rcases hp.eq_or_lt with rfl | hp
  · have h : kleinGap 0 q = q := by
      rw [kleinGap]
      ring
    rw [h]
    exact hq
  · have hne : q / p ≠ 1 := fun h => hpq ((div_eq_one_iff_eq hp.ne').1 h).symm
    have h := Real.log_lt_sub_one_of_pos (div_pos hq hp) hne
    rw [Real.log_div hq.ne' hp.ne'] at h
    have h2 := mul_lt_mul_of_pos_left h hp
    have h3 : p * (q / p - 1) = q - p := by rw [mul_sub, mul_one, mul_div_cancel₀ q hp.ne']
    rw [h3, mul_sub] at h2
    rw [kleinGap]
    linarith

/-- 雙隨機恆等式：列和、行和都是 1 時，
`Σ_ij M_ij g(p_i, q_j) = −Σ_ij M_ij p_i log q_j − Σ_i (−p_i log p_i)`。 -/
theorem klein_sum_identity {ι : Type*} [Fintype ι] (p q : ι → ℝ) (M : ι → ι → ℝ)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1)
    (hq1 : ∑ j, q j = 1) (hp1 : ∑ i, p i = 1) :
    ∑ i, ∑ j, M i j * kleinGap (p i) (q j) =
      -(∑ i, ∑ j, M i j * p i * Real.log (q j)) - ∑ i, Real.negMulLog (p i) := by
  have hA : ∑ i, ∑ j, M i j * (p i * Real.log (p i)) = ∑ i, p i * Real.log (p i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hB : ∑ i, ∑ j, M i j * p i = 1 := by
    rw [← hp1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have hC : ∑ i, ∑ j, M i j * q j = 1 := by
    rw [Finset.sum_comm, ← hq1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have hexp : ∀ i j, M i j * kleinGap (p i) (q j) =
      M i j * (p i * Real.log (p i)) - M i j * p i * Real.log (q j) - M i j * p i +
        M i j * q j := by
    intro i j
    rw [kleinGap]
    ring
  have hneg : ∑ i, Real.negMulLog (p i) = -∑ i, p i * Real.log (p i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.negMulLog]
    ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hB, hC, hneg]
  ring

/-- 純實數版的 Klein 恆等式：`q_j = e^{-βE_j}/Z`，
`β Σ_ij p_i E_j M_ij + log Z − Σ_i (−p_i log p_i) = Σ_ij M_ij g(p_i, q_j)`。 -/
theorem klein_real {ι : Type*} [Fintype ι] [Nonempty ι] (p E : ι → ℝ) (M : ι → ι → ℝ) (β : ℝ)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) (hp1 : ∑ i, p i = 1) :
    β * (∑ i, ∑ j, p i * E j * M i j) + Real.log (∑ j, Real.exp (-β * E j)) -
        ∑ i, Real.negMulLog (p i) =
      ∑ i, ∑ j, M i j * kleinGap (p i) (Real.exp (-β * E j) / ∑ k, Real.exp (-β * E k)) := by
  set Z := ∑ k, Real.exp (-β * E k) with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  have hq1 : ∑ j, Real.exp (-β * E j) / Z = 1 := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  have hid := klein_sum_identity p (fun j => Real.exp (-β * E j) / Z) M hrow hcol hq1 hp1
  have hlog : ∀ j, Real.log (Real.exp (-β * E j) / Z) = -β * E j - Real.log Z := fun j => by
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hB : ∑ i, ∑ j, M i j * p i = 1 := by
    rw [← hp1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have e : ∀ i j, M i j * p i * Real.log (Real.exp (-β * E j) / Z) =
      -β * (p i * E j * M i j) - Real.log Z * (M i j * p i) := fun i j => by
    rw [hlog]
    ring
  have hT : ∑ i, ∑ j, M i j * p i * Real.log (Real.exp (-β * E j) / Z) =
      -β * ∑ i, ∑ j, p i * E j * M i j - Real.log Z * ∑ i, ∑ j, M i j * p i := by
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hB, mul_one] at hT
  linarith

/-- 跡為 1 ⇒ 指標型別非空。 -/
theorem nonempty_of_trace_eq_one {ι : Type*} [Fintype ι] {σ : Matrix ι ι ℂ}
    (htr : trace σ = 1) : Nonempty ι := by
  rcases isEmpty_or_nonempty ι with h | h
  · exfalso
    rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at htr
    exact zero_ne_one htr
  · exact h

/-! ## 矩陣層：雙隨機矩陣與能量期望值 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- 么正矩陣的每一列：`Σ_j |W_ij|² = 1`。 -/
theorem sum_normSq_row (W : Matrix ι ι ℂ) (hW : W * star W = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrFun (congrFun hW i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h' : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, Complex.mul_conj]
  exact_mod_cast h'

/-- 么正矩陣的每一行：`Σ_i |W_ij|² = 1`。 -/
theorem sum_normSq_col (W : Matrix ι ι ℂ) (hW : star W * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrFun (congrFun hW j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h' : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  exact_mod_cast h'

/-- `tr(diag(p)·W·diag(e)·Wᴴ) = Σ_ij p_i e_j |W_ij|²`。 -/
theorem trace_diag_mul_diag (W : Matrix ι ι ℂ) (p e : ι → ℝ) :
    trace (diagonal (fun i => (p i : ℂ)) * W * diagonal (fun j => (e j : ℂ)) * star W) =
      ((∑ i, ∑ j, p i * e j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  have hA : diagonal (fun i => (p i : ℂ)) * W * diagonal (fun j => (e j : ℂ)) =
      Matrix.of fun i j => (p i : ℂ) * W i j * (e j : ℂ) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  rw [hA, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj, Complex.star_def]
  ring

/-- `W = Vᴴ U` 是么正矩陣（一邊）。 -/
theorem eigU_cross_mul_star {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) (hH : H.IsHermitian) :
    star (eigU hσ) * eigU hH * star (star (eigU hσ) * eigU hH) = 1 := by
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hH), eigU_mul_star hH,
    Matrix.one_mul, eigU_star_mul hσ]

/-- `W = Vᴴ U` 是么正矩陣（另一邊）。 -/
theorem eigU_cross_star_mul {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) (hH : H.IsHermitian) :
    star (star (eigU hσ) * eigU hH) * (star (eigU hσ) * eigU hH) = 1 := by
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hσ), eigU_mul_star hσ,
    Matrix.one_mul, eigU_star_mul hH]

/-- **能量期望值**：`tr(σH) = Σ_ij p_i E_j |W_ij|²`，`p`、`E` 是兩者的固有值，`W = Vᴴ U`。 -/
theorem trace_mul_eq_sum {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian) (hH : H.IsHermitian) :
    trace (σ * H) = ((∑ i, ∑ j, hσ.eigenvalues i * hH.eigenvalues j *
      Complex.normSq ((star (eigU hσ) * eigU hH) i j) : ℝ) : ℂ) := by
  rw [← trace_diag_mul_diag, star_mul, star_star]
  calc trace (σ * H)
      = trace (eigU hσ * diagonal (fun i => (hσ.eigenvalues i : ℂ)) * star (eigU hσ) *
          (eigU hH * diagonal (fun j => (hH.eigenvalues j : ℂ)) * star (eigU hH))) := by
        conv_lhs => rw [eigU_spectral hσ, eigU_spectral hH]
    _ = trace (diagonal (fun i => (hσ.eigenvalues i : ℂ)) * star (eigU hσ) *
          (eigU hH * diagonal (fun j => (hH.eigenvalues j : ℂ)) * star (eigU hH)) * eigU hσ) := by
        rw [Matrix.trace_mul_comm _ (eigU hσ)]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- 跡為 1 的 Hermitian 矩陣，固有值和為 1。 -/
theorem sum_eigenvalues_of_trace_eq_one {σ : Matrix ι ι ℂ} (hσ : σ.IsHermitian)
    (htr : trace σ = 1) : ∑ i, hσ.eigenvalues i = 1 := by
  have h := hσ.trace_eq_sum_eigenvalues
  have h2 : ((∑ i, hσ.eigenvalues i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_one, ← htr, h]
    -- `trace_eq_sum_eigenvalues` 的轉型是 `RCLike.ofReal`，與 `Complex.ofReal` 定義相等
    rfl
  exact Complex.ofReal_injective h2

/-! ## Klein 不等式與等號情形 -/

/-- **缺口恆等式**：`β·tr(σH) + log Z − S(σ) = Σ_ij |W_ij|² · g(p_i, q_j)`。 -/
theorem klein_gap_eq (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : trace σ = 1) :
    β * (trace (σ * H)).re + Real.log (partZ hH β) - vnEntropy σ =
      ∑ i, ∑ j, Complex.normSq ((star (eigU hσ.1) * eigU hH) i j) *
        kleinGap (hσ.1.eigenvalues i) (bw hH β j / partZ hH β) := by
  have := nonempty_of_trace_eq_one htr
  rw [trace_mul_eq_sum hσ.1 hH, Complex.ofReal_re, vnEntropy_eq_sum_eigenvalues hσ.1]
  exact klein_real _ _ (fun i j => Complex.normSq ((star (eigU hσ.1) * eigU hH) i j)) β
    (sum_normSq_row _ (eigU_cross_mul_star hσ.1 hH))
    (sum_normSq_col _ (eigU_cross_star_mul hσ.1 hH))
    (sum_eigenvalues_of_trace_eq_one hσ.1 htr)

/-- **Klein 不等式**：`S(σ) ≤ β·tr(σH) + log Z`。 -/
theorem vnEntropy_le_beta_energy_add_log (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ}
    (hσ : σ.PosSemidef) (htr : trace σ = 1) :
    vnEntropy σ ≤ β * (trace (σ * H)).re + Real.log (partZ hH β) := by
  have := nonempty_of_trace_eq_one htr
  have hZ := partZ_pos hH β
  have h := klein_gap_eq hH β hσ htr
  have hnn : 0 ≤ ∑ i, ∑ j, Complex.normSq ((star (eigU hσ.1) * eigU hH) i j) *
      kleinGap (hσ.1.eigenvalues i) (bw hH β j / partZ hH β) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (Complex.normSq_nonneg _)
        (kleinGap_nonneg (hσ.eigenvalues_nonneg i) (div_pos (Real.exp_pos _) hZ))
  linarith

/-- **等號只在 Gibbs 態**：`S(σ) = β·tr(σH) + log Z ⇔ σ = gibbs H β`。 -/
theorem vnEntropy_eq_beta_energy_add_log_iff (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ}
    (hσ : σ.PosSemidef) (htr : trace σ = 1) :
    vnEntropy σ = β * (trace (σ * H)).re + Real.log (partZ hH β) ↔ σ = gibbs H β := by
  have := nonempty_of_trace_eq_one htr
  have hZ := partZ_pos hH β
  have hq : ∀ j, 0 < bw hH β j / partZ hH β := fun j => div_pos (Real.exp_pos _) hZ
  constructor
  · intro heq
    have hgap := klein_gap_eq hH β hσ htr
    rw [heq, sub_self] at hgap
    have hin : ∀ i, 0 ≤ ∑ j, Complex.normSq ((star (eigU hσ.1) * eigU hH) i j) *
        kleinGap (hσ.1.eigenvalues i) (bw hH β j / partZ hH β) := fun i =>
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (Complex.normSq_nonneg _) (kleinGap_nonneg (hσ.eigenvalues_nonneg i) (hq j))
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hin i).1 hgap.symm
    have hterm : ∀ i j, (star (eigU hσ.1) * eigU hH) i j ≠ 0 →
        hσ.1.eigenvalues i = bw hH β j / partZ hH β := by
      intro i j hW
      by_contra hne
      have hpos : 0 < Complex.normSq ((star (eigU hσ.1) * eigU hH) i j) *
          kleinGap (hσ.1.eigenvalues i) (bw hH β j / partZ hH β) :=
        mul_pos (Complex.normSq_pos.2 hW) (kleinGap_pos (hσ.eigenvalues_nonneg i) (hq j) hne)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (Complex.normSq_nonneg _)
          (kleinGap_nonneg (hσ.eigenvalues_nonneg i) (hq j))).1 (h0 i (Finset.mem_univ i)) j
          (Finset.mem_univ j)
      linarith
    have hcomm : diagonal (fun i => (hσ.1.eigenvalues i : ℂ)) * (star (eigU hσ.1) * eigU hH) =
        (star (eigU hσ.1) * eigU hH) *
          diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) := by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hW : (star (eigU hσ.1) * eigU hH) i j = 0
      · rw [hW, mul_zero, zero_mul]
      · rw [hterm i j hW, mul_comm]
    calc σ = eigU hσ.1 * diagonal (fun i => (hσ.1.eigenvalues i : ℂ)) * star (eigU hσ.1) :=
          eigU_spectral hσ.1
      _ = eigU hσ.1 * (diagonal (fun i => (hσ.1.eigenvalues i : ℂ)) *
            (star (eigU hσ.1) * eigU hH)) * star (eigU hH) := by
          simp only [Matrix.mul_assoc, eigU_mul_star hH, Matrix.mul_one]
      _ = eigU hσ.1 * ((star (eigU hσ.1) * eigU hH) *
            diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ))) * star (eigU hH) := by
          rw [hcomm]
      _ = eigU hH * diagonal (fun j => ((bw hH β j / partZ hH β : ℝ) : ℂ)) * star (eigU hH) := by
          simp only [← Matrix.mul_assoc, eigU_mul_star hσ.1, Matrix.one_mul]
      _ = gibbs H β := (gibbs_eq_conj hH β).symm
  · rintro rfl
    rw [vnEntropy_gibbs_eq_fn hH β, trace_gibbs_mul_self hH β, Complex.ofReal_re, gibbsEntropyFn,
      energyMean]
    ring

/-- `S(gibbs H β) = β·tr(gibbs·H) + log Z`（CHAIN_DESIGN §5.2 S5 的第一條）。 -/
theorem vnEntropy_gibbs_eq_beta_energy_add_log [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    vnEntropy (gibbs H β) = β * (trace (gibbs H β * H)).re + Real.log (partZ hH β) :=
  (vnEntropy_eq_beta_energy_add_log_iff hH β (gibbs_posSemidef hH β) (trace_gibbs hH β)).2 rfl

/-- **最大熵**：能量期望值與 Gibbs 態相同的態，熵不超過 Gibbs 態。 -/
theorem vnEntropy_le_gibbs_of_energy_eq (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ}
    (hσ : σ.PosSemidef) (htr : trace σ = 1)
    (hE : (trace (σ * H)).re = (trace (gibbs H β * H)).re) :
    vnEntropy σ ≤ vnEntropy (gibbs H β) := by
  have := nonempty_of_trace_eq_one htr
  rw [vnEntropy_gibbs_eq_beta_energy_add_log hH β, ← hE]
  exact vnEntropy_le_beta_energy_add_log hH β hσ htr

/-- **最大熵（唯一）**：能量相同而不是 Gibbs 態的，熵嚴格較小。 -/
theorem vnEntropy_lt_gibbs_of_energy_eq (hH : H.IsHermitian) (β : ℝ) {σ : Matrix ι ι ℂ}
    (hσ : σ.PosSemidef) (htr : trace σ = 1)
    (hE : (trace (σ * H)).re = (trace (gibbs H β * H)).re) (hne : σ ≠ gibbs H β) :
    vnEntropy σ < vnEntropy (gibbs H β) := by
  have := nonempty_of_trace_eq_one htr
  rw [vnEntropy_gibbs_eq_beta_energy_add_log hH β, ← hE]
  exact lt_of_le_of_ne (vnEntropy_le_beta_energy_add_log hH β hσ htr)
    fun h => hne ((vnEntropy_eq_beta_energy_add_log_iff hH β hσ htr).1 h)

/-! ## 見證：等號情形不是空的 -/

/-- 純態 `|0⟩⟨0|`。 -/
def ket0Proj : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => ((![1, 0] i : ℝ) : ℂ)

theorem ket0Proj_posSemidef : ket0Proj.PosSemidef :=
  posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (by fin_cases i <;> simp)

theorem trace_ket0Proj : trace ket0Proj = 1 := by
  simp [ket0Proj, trace_diagonal, Fin.sum_univ_two]

/-- **負控制**（CHAIN_DESIGN §5.2）：`H = diag(0, 1)`、`β = ln 2` 時，
純態 `|0⟩⟨0|` 嚴格小於右邊。 -/
theorem negctrl_klein_pure_H2 :
    vnEntropy ket0Proj <
      Real.log 2 * (trace (ket0Proj * H2)).re + Real.log (partZ H2_isHermitian (Real.log 2)) := by
  refine lt_of_le_of_ne (vnEntropy_le_beta_energy_add_log H2_isHermitian _ ket0Proj_posSemidef
    trace_ket0Proj) ?_
  rw [Ne, vnEntropy_eq_beta_energy_add_log_iff H2_isHermitian _ ket0Proj_posSemidef
    trace_ket0Proj, gibbs_H2_log2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [ket0Proj, diagonal_apply_eq] at h00
  norm_num at h00

/-- 另一個溫度的 Gibbs 態（`β′ = −ln 2`）在 `β = ln 2` 下也嚴格小於右邊：
等號同時釘住了 β。 -/
theorem negctrl_klein_other_beta_H2 :
    vnEntropy (gibbs H2 (-Real.log 2)) <
      Real.log 2 * (trace (gibbs H2 (-Real.log 2) * H2)).re +
        Real.log (partZ H2_isHermitian (Real.log 2)) := by
  refine lt_of_le_of_ne (vnEntropy_le_beta_energy_add_log H2_isHermitian _
    (gibbs_posSemidef H2_isHermitian _) (trace_gibbs H2_isHermitian _)) ?_
  rw [Ne, vnEntropy_eq_beta_energy_add_log_iff H2_isHermitian _
    (gibbs_posSemidef H2_isHermitian _) (trace_gibbs H2_isHermitian _), gibbs_H2_neg_log2,
    gibbs_H2_log2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [diagonal_apply_eq] at h00
  norm_num at h00

end

end ErEpr
