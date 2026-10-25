import ErEpr.KMS

/-!
# ErEpr.KMSPair：KMS 對與「tracial ⇔ 週期」（CHAIN_DESIGN §3）

* **結構**（`KMSPair`）：ℂ-代數 `𝒜` 上的虛時一步 `ν`（代數同態，對應 `α_{iβ}`）、
  態 `ω`（線性泛函）、`ω 1 = 1`、非退化性、KMS 條件 `ω(a ν(b)) = ω(b a)`。
  這是 CHAIN_DESIGN §3.2 草稿的 **reduct**：只放 `tracial_iff_period` 需要的欄位；
  流 `α : ℂ → 𝒜 ≃ₐ 𝒜`、群律 `α_add`、`ω` 的實時不變性、反自同構 `σ` 都**不放**。
* **結構層級的定理**（`KMSPair.tracial_iff_period`）：`ω` tracial ⇔ `ν = id`。
  （→ 用非退化性：`ω(a(ν b − b)) = ω(b a) − ω(a b) = 0`；← 直接。）
* **交換代數**（`KMSPair.ofComm`）：交換代數上 `ν` 必為恆等。
* **矩陣實例**（`gibbsKMSPair`）：`ν = nuStep`、`ω a = tr(gibbs · a)`；
  非退化性由 Gibbs 態可逆得到（`gibbs_mul_inv`）。
* **推論**（`gibbs_tracial_iff_scalar`）：Gibbs 態 tracial ⇔ `e^{-βH}` 是純量。
* **負控制**：
  * `negctrl_gibbs_not_tracial`：`H = diag(0, 1)`、`β ≠ 0` 時 Gibbs 態不 tracial；
  * `negctrl_nondeg_needed`：拿掉非退化性，`ℂ × ℂ` 上有 tracial 而 `ν ≠ id` 的例子（T1 演習的正面版）。
* **不同構**（`no_ringHom_matrix_to_comm`）：`M₂(ℂ)` 到任何非平凡交換環沒有保 1 環同態。

範圍（引用前請讀）：
* 物理讀法（只在說明文字裡）：ER 側（座標函數，交換代數）必定 tracial，β 被剛性釘在週期上；
  EPR 側（矩陣代數）只在 `H` 純量時 tracial。溫度那一行的等號是**單向特化**（CHAIN_DESIGN §3.3）：
  ER 決定 β，EPR 把它吃進去，兩側不等價。兩側最多共享 reduct，到不了同構（§3.4）。
* 本檔不實作 ER 側的任何具體交換代數；`ofComm` 只是結構層級的定理。
-/

namespace ErEpr

open Matrix

noncomputable section

/-- **KMS 對**（CHAIN_DESIGN §3.2 的 reduct）。
`ν` 對應虛時一步 `α_{iβ}`，`ω` 是態。流 `α`、群律、實時不變性與反自同構 `σ` 都不放。 -/
structure KMSPair (𝒜 : Type*) [Ring 𝒜] [Algebra ℂ 𝒜] where
  /-- 虛時一步 `α_{iβ}`。 -/
  ν : 𝒜 →ₐ[ℂ] 𝒜
  /-- 態。 -/
  ω : 𝒜 →ₗ[ℂ] ℂ
  ω_one : ω 1 = 1
  nondeg : ∀ x, (∀ a, ω (a * x) = 0) → x = 0
  kms : ∀ a b, ω (a * ν b) = ω (b * a)

namespace KMSPair

section General

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

/-- **tracial ⇔ 週期**：在 KMS 對上，`ω` tracial 當且僅當虛時一步是恆等。 -/
theorem tracial_iff_period (P : KMSPair 𝒜) :
    (∀ a b, P.ω (a * b) = P.ω (b * a)) ↔ ∀ b, P.ν b = b := by
  constructor
  · intro htr b
    refine sub_eq_zero.mp (P.nondeg (P.ν b - b) fun a => ?_)
    rw [mul_sub, map_sub, P.kms, htr, sub_self]
  · intro hν a b
    rw [← P.kms a b, hν]

end General

/-- **交換代數**：交換代數上的 KMS 對，虛時一步必為恆等。
物理讀法：ER 側（座標函數）β 被剛性釘在週期上。 -/
theorem ofComm {𝒜 : Type*} [CommRing 𝒜] [Algebra ℂ 𝒜] (P : KMSPair 𝒜) : ∀ b, P.ν b = b :=
  P.tracial_iff_period.mp fun a b => by rw [mul_comm]

end KMSPair

/-! ## 矩陣實例 -/

section MatrixInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gibbs 態 `a ↦ tr(gibbs H β · a)`。 -/
def gibbsState (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun a := trace (gibbs H β * a)
  map_add' a b := by simp only [Matrix.mul_add, trace_add]
  map_smul' c a := by simp only [Matrix.mul_smul, trace_smul, RingHom.id_apply]

/-- Gibbs 態的右逆：`gibbs · (Z • e^{βH}) = 1`。 -/
theorem gibbs_mul_inv [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    gibbs H β * (trace (NormedSpace.exp (-(β : ℂ) • H)) • NormedSpace.exp ((β : ℂ) • H)) = 1 := by
  rw [gibbs, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ (trace_exp_neg_smul_ne_zero hH β), one_smul, exp_neg_mul_exp]

/-- Gibbs 態可逆。 -/
theorem gibbs_isUnit [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    IsUnit (gibbs H β) :=
  ⟨⟨_, _, gibbs_mul_inv hH β, mul_eq_one_comm.mp (gibbs_mul_inv hH β)⟩, rfl⟩

/-- **矩陣實例**：`ν = nuStep`，`ω a = tr(gibbs H β · a)`。 -/
def gibbsKMSPair [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    KMSPair (Matrix ι ι ℂ) where
  ν := nuStepAlgHom H β
  ω := gibbsState H β
  ω_one := by
    show trace (gibbs H β * 1) = 1
    rw [Matrix.mul_one, trace_gibbs hH β]
  nondeg x hx := by
    refine Matrix.ext_iff_trace_mul_left.mpr fun y => ?_
    have h : trace (gibbs H β * ((trace (NormedSpace.exp (-(β : ℂ) • H)) •
        NormedSpace.exp ((β : ℂ) • H)) * y * x)) = 0 :=
      hx ((trace (NormedSpace.exp (-(β : ℂ) • H)) • NormedSpace.exp ((β : ℂ) • H)) * y)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, gibbs_mul_inv hH β, Matrix.one_mul] at h
    rw [Matrix.mul_zero, trace_zero]
    exact h
  kms a b := by
    show trace (gibbs H β * (a * nuStep H β b)) = trace (gibbs H β * (b * a))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact gibbs_isKMS H β a b

theorem gibbsKMSPair_ω [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ)
    (x : Matrix ι ι ℂ) : (gibbsKMSPair hH β).ω x = trace (gibbs H β * x) := rfl

theorem gibbsKMSPair_ν [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ)
    (b : Matrix ι ι ℂ) : (gibbsKMSPair hH β).ν b = nuStep H β b := rfl

/-- **推論**：Gibbs 態 tracial ⇔ `e^{-βH}` 是純量矩陣。
物理讀法（只在說明文字裡）：ER 側（交換代數）必定 tracial；EPR 側只在 `H` 純量時 tracial。
溫度那一行的等號是單向特化（CHAIN_DESIGN §3.3）。 -/
theorem gibbs_tracial_iff_scalar [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (∀ a b : Matrix ι ι ℂ, trace (gibbs H β * (a * b)) = trace (gibbs H β * (b * a))) ↔
      ∃ c : ℂ, NormedSpace.exp (-(β : ℂ) • H) = c • (1 : Matrix ι ι ℂ) := by
  have key : (∀ a b : Matrix ι ι ℂ, trace (gibbs H β * (a * b)) = trace (gibbs H β * (b * a))) ↔
      ∀ b, nuStep H β b = b := (gibbsKMSPair hH β).tracial_iff_period
  rw [key]
  constructor
  · intro hν
    obtain ⟨c, hc⟩ :=
      (mem_range_scalar_iff_commute_single (M := NormedSpace.exp (-(β : ℂ) • H))).mpr
        fun i j _ => ((conj_eq_self_iff (b := single i j 1) (exp_neg_mul_exp H β)
          (exp_mul_exp_neg H β)).mp (hν (single i j 1))).symm
    exact ⟨c, by rw [← hc, scalar_apply, smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩ b
    refine (conj_eq_self_iff (b := b) (exp_neg_mul_exp H β) (exp_mul_exp_neg H β)).mpr ?_
    rw [hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-! ## 負控制 -/

/-- **負控制（一般形）**：實對角 `H` 有兩個不同的固有值 `E i ≠ E j`、`β ≠ 0` 時，
Gibbs 態不 tracial。見證：`a = E_{ij}`、`b = E_{ji}`，兩邊分別是 `w_i/Z` 與 `w_j/Z`。 -/
theorem negctrl_diag_not_tracial {E : ι → ℝ} {i j : ι} (hE : E i ≠ E j) {β : ℝ} (hβ : β ≠ 0) :
    ¬ ∀ a b : Matrix ι ι ℂ, trace (gibbs (diagonal fun k => (E k : ℂ)) β * (a * b)) =
      trace (gibbs (diagonal fun k => (E k : ℂ)) β * (b * a)) := by
  intro h
  have h1 := h (single i j 1) (single j i 1)
  rw [single_mul_single_same, single_mul_single_same, trace_mul_single, trace_mul_single,
    gibbs_diagonal_real, diagonal_apply_eq, diagonal_apply_eq] at h1
  simp only [mul_one, MulOpposite.op_one, one_smul] at h1
  have hS : (∑ k, Real.exp (-β * E k)) ≠ 0 :=
    (Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩).ne'
  have h2 := Real.exp_injective ((div_left_inj' hS).mp (Complex.ofReal_injective h1))
  have h3 : β * (E i - E j) = 0 := by linear_combination -h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact hβ h4
  · exact hE (sub_eq_zero.mp h4)

/-- **負控制（實例）**：`H = diag(0, 1)`、`β ≠ 0` 時 Gibbs 態不 tracial。 -/
theorem negctrl_gibbs_not_tracial {β : ℝ} (hβ : β ≠ 0) :
    ¬ ∀ a b : Matrix (Fin 2) (Fin 2) ℂ,
      trace (gibbs H2 β * (a * b)) = trace (gibbs H2 β * (b * a)) :=
  negctrl_diag_not_tracial (E := ![0, 1]) (i := 0) (j := 1) (by norm_num) hβ

end MatrixInstance

/-- **負控制：非退化性不可省**（T1 演習的正面版）。在 `ℂ × ℂ` 上取 `ω = 第一分量`、
`ν(x, y) = (x, x)`：`ω 1 = 1`、KMS 條件成立、`ω` tracial，但 `ν ≠ id`。
`ω` 在 `(0, 1)` 上退化，所以這不是 `KMSPair`。 -/
theorem negctrl_nondeg_needed :
    ∃ (ν : ℂ × ℂ →ₐ[ℂ] ℂ × ℂ) (ω : ℂ × ℂ →ₗ[ℂ] ℂ), ω 1 = 1 ∧
      (∀ a b, ω (a * ν b) = ω (b * a)) ∧ (∀ a b, ω (a * b) = ω (b * a)) ∧ ∃ b, ν b ≠ b := by
  refine ⟨(Algebra.ofId ℂ (ℂ × ℂ)).comp (AlgHom.fst ℂ ℂ ℂ), LinearMap.fst ℂ ℂ ℂ, rfl,
    fun a b => ?_, fun a b => ?_, ⟨(0, 1), fun h => ?_⟩⟩
  · show a.1 * b.1 = b.1 * a.1
    exact mul_comm _ _
  · show a.1 * b.1 = b.1 * a.1
    exact mul_comm _ _
  · simpa using congrArg Prod.snd h

/-- **不同構**（CHAIN_DESIGN §3.4）：`M₂(ℂ)` 到任何非平凡交換環 `R` 沒有保 1 的環同態。
證法：`f(E₀₀) = f(E₀₁)f(E₁₀) = f(E₁₀)f(E₀₁) = f(E₁₁) =: x`，`x² = f(E₀₀E₁₁) = 0`，
`2x = f(1) = 1`，所以 `1 = (2x)² = 4x² = 0`。
物理讀法：矩陣側與交換（座標函數）側不是同一物件的兩種表示，最多共享 reduct。 -/
theorem no_ringHom_matrix_to_comm {R : Type*} [CommRing R] [Nontrivial R] :
    ¬ ∃ _ : Matrix (Fin 2) (Fin 2) ℂ →+* R, True := by
  rintro ⟨f, -⟩
  have e00 : (single 0 0 1 : Matrix (Fin 2) (Fin 2) ℂ) =
      (single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ) * (single 1 0 1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [single_mul_single_same, mul_one]
  have e11 : (single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) =
      (single 1 0 1 : Matrix (Fin 2) (Fin 2) ℂ) * (single 0 1 1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [single_mul_single_same, mul_one]
  have e0 : (single 0 0 1 : Matrix (Fin 2) (Fin 2) ℂ) *
      (single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
    single_mul_single_of_ne 1 0 0 1 (by decide) 1
  have e1 : (single 0 0 1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← diagonal_one, ← sum_single_eq_diagonal, Fin.sum_univ_two]
  have hx : f (single 0 0 1) = f (single 1 1 1) := by
    rw [e00, e11, map_mul, map_mul, mul_comm]
  have h0 : f (single 0 0 1) * f (single 1 1 1) = 0 := by rw [← map_mul, e0, map_zero]
  have h1 : f (single 0 0 1) + f (single 1 1 1) = 1 := by rw [← map_add, e1, map_one]
  rw [← hx] at h0 h1
  have h2 : (1 : R) = 0 := by
    linear_combination (-(f (single 0 0 1) + f (single 0 0 1) + 1)) * h1 + 4 * h0
  exact one_ne_zero h2

end

end ErEpr
