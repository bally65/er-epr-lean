import ErEpr.Triangle

/-!
# ErEpr.Modular：模哈密頓量與相對熵（`docs/TRIANGLE.md` §5 的 T-c，有限維 Casini 形式）

任何滿秩、跡 1 的參考態 `ρ₀ = U·diag(q)·Uᴴ`（`U` 么正、`q > 0`、`Σq = 1`）都可以看成
某個「哈密頓量」在 `β = 1` 的 Gibbs 態：取**模哈密頓量** `K = −log ρ₀ = U·diag(−log q)·Uᴴ`
（`modHamOf`）。

* 保真：`exp(−K) = ρ₀`（`exp_neg_modHamOf`）、`gibbs K 1 = ρ₀`（`gibbs_modHamOf`）、
  `Z = 1`（`partZ_modHamOf`）；Gibbs 參考態的模哈密頓量就是 `βH + log Z`（`modHamOf_gibbs`）。
* **T-c**（`entropy_le_modular`）：任何態 `σ` 都滿足 `ΔS ≤ Δ⟨K⟩`，
  即 `S(σ) − S(ρ₀) ≤ tr(σK) − tr(ρ₀K)`；等號只在 `σ = ρ₀`（`entropy_eq_modular_iff`）。
  這是 Casini（2008）相對熵版 Bekenstein 界的有限維骨架。
* **相對熵** `D(σ‖ρ₀) = tr(σK) − S(σ)`（`relEntropyOf`）：`D ≥ 0`（`relEntropyOf_nonneg`），
  `D = 0 ⇔ σ = ρ₀`（`relEntropyOf_eq_zero_iff`）；對易（對角）時退化成古典 KL 散度
  `Σ p_i (log p_i − log q_i)`（`relEntropyOf_diagonal`）。
* 標準形（`modHam`、`entropy_le_modHam`）：用 `ρ₀` 自己的固有分解，只需要 `ρ₀` 正定。
* 負控制（`negctrl_modular_not_fullRank`）：參考態不滿秩時（`q = (1, 0)`），
  Lean 的 `log 0 = 0` 讓 `K = 0`，不等式對最大混合態失敗：`q > 0` 不能拿掉。

範圍（引用前請讀）：
* 這只到「`ΔS ≤ Δ⟨K⟩`」。Casini 的論證還需要「真空在 Rindler 楔裡的模哈密頓量是
  `2π × boost 生成元`」（Bisognano–Wichmann）與「`Δ⟨K⟩ ≤ 2πRE`」，兩者都是量子場論的內容，
  本庫沒有。所以本檔**不**證 Bekenstein 界。
* `K` 的定義依賴所選的對角化 `(U, q)`；標準形用 `ρ₀` 的固有分解。
  「Hermitian 的 `exp` 反函數唯一」本庫沒有證，所以不同對角化給出同一個 `K` 這件事未證
  （每個對角化各自都滿足 `exp(−K) = ρ₀` 與上面所有定理）。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 模哈密頓量 -/

/-- 由對角化 `ρ₀ = U·diag(q)·Uᴴ` 給出的模哈密頓量 `K = U·diag(−log q)·Uᴴ`。 -/
def modHamOf (U : Matrix ι ι ℂ) (q : ι → ℝ) : Matrix ι ι ℂ :=
  U * diagonal (fun j => ((-Real.log (q j) : ℝ) : ℂ)) * star U

theorem modHamOf_isHermitian (U : Matrix ι ι ℂ) (q : ι → ℝ) : (modHamOf U q).IsHermitian := by
  have hd : star (fun j => ((-Real.log (q j) : ℝ) : ℂ)) = fun j => ((-Real.log (q j) : ℝ) : ℂ) := by
    funext j
    simp
  show (modHamOf U q)ᴴ = modHamOf U q
  rw [modHamOf, conj_diag_conjTranspose, hd]

/-- **保真**：`exp(−K) = U·diag(q)·Uᴴ`（需要 `q > 0`）。 -/
theorem exp_neg_modHamOf (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ} (hq : ∀ j, 0 < q j) :
    NormedSpace.exp (-((1 : ℝ) : ℂ) • modHamOf (U : Matrix ι ι ℂ) q) =
      (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ) := by
  have hinv : (U : Matrix ι ι ℂ)⁻¹ = star (U : Matrix ι ι ℂ) :=
    inv_eq_right_inv (Unitary.coe_mul_star_self U)
  have hd : (-((1 : ℝ) : ℂ)) • (fun j => ((-Real.log (q j) : ℝ) : ℂ)) =
      fun j => ((Real.log (q j) : ℝ) : ℂ) := by
    funext j
    simp
  have hK : -((1 : ℝ) : ℂ) • modHamOf (U : Matrix ι ι ℂ) q =
      (U : Matrix ι ι ℂ) * diagonal (fun j => ((Real.log (q j) : ℝ) : ℂ)) *
        (U : Matrix ι ι ℂ)⁻¹ := by
    rw [modHamOf, hinv, ← hd, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  have he : (fun j => ((Real.exp (Real.log (q j)) : ℝ) : ℂ)) = fun j => (q j : ℂ) := by
    funext j
    rw [Real.exp_log (hq j)]
  rw [hK, Matrix.exp_conj _ _ Unitary.isUnit_coe, Matrix.exp_diagonal, nexp_pi_ofReal, hinv, he]

theorem trace_unitary_conj_diag (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ} (hq1 : ∑ j, q j = 1) :
    trace ((U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ)) = 1 := by
  rw [trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal,
    ← Complex.ofReal_sum, hq1, Complex.ofReal_one]

/-- **保真**：`ρ₀` 是 `K` 在 `β = 1` 的 Gibbs 態。 -/
theorem gibbs_modHamOf (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ} (hq : ∀ j, 0 < q j)
    (hq1 : ∑ j, q j = 1) :
    gibbs (modHamOf (U : Matrix ι ι ℂ) q) 1 =
      (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ) := by
  rw [gibbs, exp_neg_modHamOf U hq, trace_unitary_conj_diag U hq1, inv_one, one_smul]

/-- **保真**：`K` 的配分函數是 1。 -/
theorem partZ_modHamOf (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ} (hq : ∀ j, 0 < q j)
    (hq1 : ∑ j, q j = 1) :
    partZ (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 = 1 := by
  have h := trace_exp_neg_smul_eq (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1
  rw [exp_neg_modHamOf U hq, trace_unitary_conj_diag U hq1] at h
  exact Complex.ofReal_injective (by rw [Complex.ofReal_one]; exact h.symm)

/-- **保真**：Gibbs 參考態的模哈密頓量是 `βH + log Z`。 -/
theorem modHamOf_gibbs [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    modHamOf (eigU hH) (fun j => bw hH β j / partZ hH β) =
      (β : ℂ) • H + (Real.log (partZ hH β) : ℂ) • 1 := by
  have hZ := partZ_pos hH β
  have hd : (fun j => ((-Real.log (bw hH β j / partZ hH β) : ℝ) : ℂ)) =
      (β : ℂ) • (fun j => (hH.eigenvalues j : ℂ)) + fun _ => (Real.log (partZ hH β) : ℂ) := by
    funext j
    rw [bw, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  -- `diagonal_add` 是逐點 lambda 形式；Pi 加法與它定義相等
  have hdiag : diagonal ((β : ℂ) • (fun j => (hH.eigenvalues j : ℂ)) +
      fun _ => (Real.log (partZ hH β) : ℂ)) =
      diagonal ((β : ℂ) • (fun j => (hH.eigenvalues j : ℂ))) +
        diagonal (fun _ : ι => (Real.log (partZ hH β) : ℂ)) :=
    (diagonal_add _ _).symm
  rw [modHamOf, hd, hdiag, Matrix.mul_add, Matrix.add_mul, diagonal_smul, Matrix.mul_smul,
    Matrix.smul_mul, ← eigU_spectral hH, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, eigU_mul_star hH]

/-! ## T-c：ΔS ≤ Δ⟨K⟩ -/

/-- **T-c（有限維 Casini 形式）**：參考態 `ρ₀ = U·diag(q)·Uᴴ`（`q > 0`、`Σq = 1`），
任何態 `σ`：`S(σ) − S(ρ₀) ≤ tr(σK) − tr(ρ₀K)`。 -/
theorem entropy_le_modular {ρ₀ : Matrix ι ι ℂ} (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ}
    (hρ : ρ₀ = (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ))
    (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : trace σ = 1) :
    vnEntropy σ - vnEntropy ρ₀ ≤
      (trace (σ * modHamOf (U : Matrix ι ι ℂ) q)).re -
        (trace (ρ₀ * modHamOf (U : Matrix ι ι ℂ) q)).re := by
  have h := reservoir_entropy_le_beta_heat (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 hσ htr
  rw [gibbs_modHamOf U hq hq1, one_mul, ← hρ] at h
  exact h

/-- 等號只在 `σ = ρ₀`。 -/
theorem entropy_eq_modular_iff {ρ₀ : Matrix ι ι ℂ} (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ}
    (hρ : ρ₀ = (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ))
    (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : trace σ = 1) :
    vnEntropy σ - vnEntropy ρ₀ =
        (trace (σ * modHamOf (U : Matrix ι ι ℂ) q)).re -
          (trace (ρ₀ * modHamOf (U : Matrix ι ι ℂ) q)).re ↔ σ = ρ₀ := by
  have h := reservoir_entropy_eq_beta_heat_iff (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 hσ htr
  rw [gibbs_modHamOf U hq hq1, one_mul, ← hρ] at h
  exact h

/-! ## 相對熵 -/

/-- 相對熵 `D(σ‖ρ₀) = tr(σK) − S(σ)`，`K = −log ρ₀`（由對角化 `(U, q)` 給出）。 -/
def relEntropyOf (U : Matrix ι ι ℂ) (q : ι → ℝ) (σ : Matrix ι ι ℂ) : ℝ :=
  (trace (σ * modHamOf U q)).re - vnEntropy σ

/-- **相對熵非負**（Klein 不等式的通常形式）。 -/
theorem relEntropyOf_nonneg (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ} (hq : ∀ j, 0 < q j)
    (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (htr : trace σ = 1) :
    0 ≤ relEntropyOf (U : Matrix ι ι ℂ) q σ := by
  have h := vnEntropy_le_beta_energy_add_log (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 hσ htr
  rw [partZ_modHamOf U hq hq1, Real.log_one, add_zero, one_mul] at h
  rw [relEntropyOf]
  linarith

/-- **相對熵為零 ⇔ 兩態相同**。 -/
theorem relEntropyOf_eq_zero_iff {ρ₀ : Matrix ι ι ℂ} (U : unitary (Matrix ι ι ℂ)) {q : ι → ℝ}
    (hρ : ρ₀ = (U : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) * star (U : Matrix ι ι ℂ))
    (hq : ∀ j, 0 < q j) (hq1 : ∑ j, q j = 1) {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : trace σ = 1) :
    relEntropyOf (U : Matrix ι ι ℂ) q σ = 0 ↔ σ = ρ₀ := by
  have h := vnEntropy_eq_beta_energy_add_log_iff (modHamOf_isHermitian (U : Matrix ι ι ℂ) q) 1 hσ
    htr
  rw [partZ_modHamOf U hq hq1, Real.log_one, add_zero, one_mul, gibbs_modHamOf U hq hq1,
    ← hρ] at h
  rw [relEntropyOf, ← h]
  constructor <;> intro h' <;> linarith

/-- **保真**：對易（對角）時退化成古典 KL 散度 `Σ p_i (log p_i − log q_i)`。 -/
theorem relEntropyOf_diagonal (p q : ι → ℝ) :
    relEntropyOf 1 q (diagonal fun i => (p i : ℂ)) =
      ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  rw [relEntropyOf, modHamOf, Matrix.one_mul, star_one, Matrix.mul_one, diagonal_mul_diagonal,
    trace_diagonal, vnEntropy_diagonal, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.negMulLog]
  ring

/-! ## 標準形：用 ρ₀ 自己的固有分解 -/

/-- 標準的模哈密頓量 `K = −log ρ₀`，用 `ρ₀` 的固有分解。 -/
def modHam {ρ₀ : Matrix ι ι ℂ} (h : ρ₀.IsHermitian) : Matrix ι ι ℂ :=
  modHamOf (eigU h) h.eigenvalues

/-- **T-c 標準形**：`ρ₀` 正定、跡 1。 -/
theorem entropy_le_modHam {ρ₀ : Matrix ι ι ℂ} (h0 : ρ₀.PosDef) (htr0 : trace ρ₀ = 1)
    {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (htr : trace σ = 1) :
    vnEntropy σ - vnEntropy ρ₀ ≤
      (trace (σ * modHam h0.1)).re - (trace (ρ₀ * modHam h0.1)).re :=
  entropy_le_modular h0.1.eigenvectorUnitary (eigU_spectral h0.1) h0.eigenvalues_pos
    (sum_eigenvalues_of_trace_eq_one h0.1 htr0) hσ htr

/-! ## 負控制：參考態必須滿秩 -/

/-- **負控制**：`q = (1, 0)`（參考態 `|0⟩⟨0|`，不滿秩）時，`log 0 = 0` 讓 `K = 0`，
而最大混合態的 `ΔS = ln 2 > 0 = Δ⟨K⟩`。 -/
theorem negctrl_modular_not_fullRank :
    ¬ (vnEntropy (diagonal fun i => ((![1 / 2, 1 / 2] i : ℝ) : ℂ)) - vnEntropy ket0Proj ≤
        (trace ((diagonal fun i => ((![1 / 2, 1 / 2] i : ℝ) : ℂ)) * modHamOf 1 ![1, 0])).re -
          (trace (ket0Proj * modHamOf 1 ![1, 0])).re) := by
  have hK : modHamOf (1 : Matrix (Fin 2) (Fin 2) ℂ) ![1, 0] = 0 := by
    rw [modHamOf, Matrix.one_mul, star_one, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hS1 : vnEntropy (diagonal fun i => ((![1 / 2, 1 / 2] i : ℝ) : ℂ)) = Real.log 2 := by
    rw [vnEntropy_diagonal, Fin.sum_univ_two]
    simp [Real.negMulLog]
    ring
  have hS0 : vnEntropy ket0Proj = 0 := by
    rw [ket0Proj, vnEntropy_diagonal, Fin.sum_univ_two]
    simp
  rw [hK, Matrix.mul_zero, Matrix.mul_zero, trace_zero, Complex.zero_re, sub_self, not_le, hS1,
    hS0]
  linarith [Real.log_pos one_lt_two]

end

end ErEpr
