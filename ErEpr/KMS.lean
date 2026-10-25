import ErEpr.NoGo

/-!
# ErEpr.KMS：KMS 條件與 Gibbs 態的唯一性（CHAIN_DESIGN §5.2 S2）

* **虛時一步**（`nuStep`）：`ν_β(b) = e^{-βH} b e^{βH}`。
  約定：實時流 `α_t(b) = e^{itH} b e^{-itH}`，複化 `α_z(b) = e^{izH} b e^{-izH}`，`ν_β = α_{iβ}`。
  `nuStep` 保乘法、保 1（`nuStep_mul`、`nuStep_one`），包成 ℂ-代數同態是 `nuStepAlgHom`。
* **KMS 條件**（`IsKMS`）：`∀ a b, tr(σ a ν_β(b)) = tr(σ b a)`。
  CHAIN_DESIGN §5.2 的寫法 `ω(A α_t B) = ω(α_{t−iβ}(B) A)` 在 `t = 0` 取 `B := ν_β(b)`
  就是本檔的形式（`α_{−iβ} ∘ ν_β = id`）；一般 `t` 還需要 `ω` 對實時流不變，本檔不談。
* **順向**（`gibbs_isKMS`）：Gibbs 態滿足 KMS 條件（循環跡加 `e^{βH} e^{-βH} = 1`）。
* **逆向唯一**（`isKMS_unique`）：`tr σ = 1` 且 `σ` 滿足 KMS 條件，則 `σ = gibbs H β`。
  證明：KMS ⇒ `∀ b, e^{-βH} b e^{βH} σ = σ b`（跡配對非退化）⇒ `T := e^{βH} σ` 與一切交換
  ⇒ `T` 是純量 ⇒ `σ = c e^{-βH}` ⇒ `tr σ = 1` 定出 `c = 1/Z`。
  不需要 `H` Hermitian，也不需要 `ι` 非空（空的時候 `tr σ = 0 ≠ 1`，前提不成立）。
* **與 T2 接起來**：TFD 的 A 側約化態是 `H` 的 KMS 態（`tfd_ptrB_isKMS`），
  B 側約化態是 `Hᵀ` 的 KMS 態（`tfd_ptrA_isKMS`，經 `gibbs_transpose`）。
* **負控制**（`negctrl_scalar_not_kms`、`negctrl_maxMixed_not_kms`）：
  `H` 有兩個不同的固有值、`β ≠ 0` 時，純量態（含最大混合態 `1/2`）**不**滿足 KMS 條件。

範圍（引用前請讀）：
* 物理讀法是「給定 `(H, β)`，KMS 條件唯一刻畫態」：跡為 1 的 KMS 態只有 Gibbs 態。
  反過來「態決定 β」（`H` 非純量時 `gibbs H β = gibbs H β'` ⇒ `β = β'`）本檔**未證**。
  這裡沒有形式化任何時空幾何，也不談「視界光滑 ⇒ KMS」那一步（CHAIN_DESIGN §1 的 h）。
* 定理陳述只談矩陣；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 指數的互逆與實對角版 -/

/-- `e^{-βH} e^{βH} = 1`（`Matrix.exp_add_of_commute`，`-X` 與 `X` 交換）。 -/
theorem exp_neg_mul_exp (H : Matrix ι ι ℂ) (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • H) * NormedSpace.exp ((β : ℂ) • H) = 1 := by
  have hc : Commute (-((β : ℂ) • H)) ((β : ℂ) • H) := (Commute.refl _).neg_left
  rw [neg_smul, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

/-- `e^{βH} e^{-βH} = 1`。 -/
theorem exp_mul_exp_neg (H : Matrix ι ι ℂ) (β : ℝ) :
    NormedSpace.exp ((β : ℂ) • H) * NormedSpace.exp (-(β : ℂ) • H) = 1 := by
  have hc : Commute ((β : ℂ) • H) (-((β : ℂ) • H)) := (Commute.refl _).neg_right
  rw [neg_smul, ← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]

/-- 實對角矩陣的 `exp(βH)`（`exp_neg_smul_diagonal` 的正號版）。 -/
theorem exp_smul_diagonal (E : ι → ℝ) (β : ℝ) :
    NormedSpace.exp ((β : ℂ) • diagonal (fun i => (E i : ℂ))) =
      diagonal (fun i => ((Real.exp (β * E i) : ℝ) : ℂ)) := by
  have hd : (β : ℂ) • (fun i => (E i : ℂ)) = fun i => ((β * E i : ℝ) : ℂ) := by
    funext i; simp
  rw [← diagonal_smul, hd, Matrix.exp_diagonal, nexp_pi_ofReal]

/-! ## 虛時一步 -/

/-- **虛時一步** `ν_β(b) = e^{-βH} · b · e^{βH}`。
約定：`α_z(b) = e^{izH} b e^{-izH}`，`ν_β = α_{iβ}`（代入 `z = iβ`：`e^{i·iβ·H} = e^{-βH}`）。 -/
def nuStep (H : Matrix ι ι ℂ) (β : ℝ) (b : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp (-(β : ℂ) • H) * b * NormedSpace.exp ((β : ℂ) • H)

/-- 共軛保乘法（一般版）：`Q P = 1` 時 `b ↦ P b Q` 保乘法。 -/
theorem conj_mul_conj {P Q : Matrix ι ι ℂ} (h : Q * P = 1) (a b : Matrix ι ι ℂ) :
    P * (a * b) * Q = P * a * Q * (P * b * Q) := by
  calc P * (a * b) * Q = P * a * (Q * P) * b * Q := by
        rw [h, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = P * a * Q * (P * b * Q) := by simp only [Matrix.mul_assoc]

/-- `ν_β` 保乘法。 -/
theorem nuStep_mul (H : Matrix ι ι ℂ) (β : ℝ) (a b : Matrix ι ι ℂ) :
    nuStep H β (a * b) = nuStep H β a * nuStep H β b :=
  conj_mul_conj (exp_mul_exp_neg H β) a b

/-- `ν_β` 保 1。 -/
theorem nuStep_one (H : Matrix ι ι ℂ) (β : ℝ) : nuStep H β 1 = 1 := by
  rw [nuStep, Matrix.mul_one, exp_neg_mul_exp]

/-- `ν_β` 的線性部分。 -/
def nuStepLinear (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := nuStep H β
  map_add' a b := by simp only [nuStep, Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by simp only [nuStep, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- `ν_β` 包成 ℂ-代數同態。 -/
def nuStepAlgHom (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ →ₐ[ℂ] Matrix ι ι ℂ :=
  AlgHom.ofLinearMap (nuStepLinear H β) (nuStep_one H β) (nuStep_mul H β)

theorem nuStepAlgHom_apply (H : Matrix ι ι ℂ) (β : ℝ) (b : Matrix ι ι ℂ) :
    nuStepAlgHom H β b = nuStep H β b := rfl

/-- `E F = 1 = F E` 時，`E b F = b` 等價於 `b` 與 `E` 交換。 -/
theorem conj_eq_self_iff {E F b : Matrix ι ι ℂ} (hEF : E * F = 1) (hFE : F * E = 1) :
    E * b * F = b ↔ E * b = b * E := by
  constructor
  · intro h
    calc E * b = E * b * (F * E) := by rw [hFE, Matrix.mul_one]
      _ = E * b * F * E := by simp only [Matrix.mul_assoc]
      _ = b * E := by rw [h]
  · intro h
    rw [h, Matrix.mul_assoc, hEF, Matrix.mul_one]

/-! ## KMS 條件 -/

/-- **KMS 條件**（對態 `σ`）：`∀ a b, tr(σ a ν_β(b)) = tr(σ b a)`。 -/
def IsKMS (σ H : Matrix ι ι ℂ) (β : ℝ) : Prop :=
  ∀ a b : Matrix ι ι ℂ, trace (σ * a * nuStep H β b) = trace (σ * b * a)

/-- 循環跡的核心一步：`F E = 1` 時 `tr(E a (E b F)) = tr(E b a)`。 -/
theorem trace_conj_cycle {E F : Matrix ι ι ℂ} (hFE : F * E = 1) (a b : Matrix ι ι ℂ) :
    trace (E * a * (E * b * F)) = trace (E * b * a) := by
  have h1 : E * a * (E * b * F) = E * a * E * b * F := by simp only [Matrix.mul_assoc]
  rw [h1, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hFE,
    Matrix.one_mul, trace_mul_comm (E * b) a, Matrix.mul_assoc]

/-- **S2 順向**：Gibbs 態滿足 KMS 條件。對任何 `H`（不必 Hermitian）、任何 β。 -/
theorem gibbs_isKMS (H : Matrix ι ι ℂ) (β : ℝ) : IsKMS (gibbs H β) H β := by
  intro a b
  simp only [gibbs, nuStep, Matrix.smul_mul, trace_smul]
  rw [trace_conj_cycle (exp_mul_exp_neg H β)]

/-- **S2 逆向的代數核心**：`F E = 1 = E F`、`tr σ = 1`，且
`∀ a b, tr(σ a (E b F)) = tr(σ b a)`，則 `σ = (tr E)⁻¹ • E`。 -/
theorem kms_core {σ E F : Matrix ι ι ℂ} (hFE : F * E = 1) (hEF : E * F = 1)
    (hk : ∀ a b, trace (σ * a * (E * b * F)) = trace (σ * b * a)) (hσ : trace σ = 1) :
    σ = (trace E)⁻¹ • E := by
  -- 第一步：跡配對非退化 ⇒ `∀ b, E b F σ = σ b`
  have hstar : ∀ b, E * b * F * σ = σ * b := by
    intro b
    refine Matrix.ext_iff_trace_mul_right.mpr fun x => ?_
    rw [← hk x b, trace_mul_comm (σ * x) (E * b * F), Matrix.mul_assoc (E * b * F)]
  -- 第二步：`T := F σ` 與一切交換
  have hcomm : ∀ b, Commute b (F * σ) := by
    intro b
    show b * (F * σ) = F * σ * b
    calc b * (F * σ) = F * E * b * F * σ := by rw [hFE, Matrix.one_mul, Matrix.mul_assoc]
      _ = F * (E * b * F * σ) := by simp only [Matrix.mul_assoc]
      _ = F * σ * b := by rw [hstar b, Matrix.mul_assoc]
  -- 第三步：`T` 是純量，所以 `σ = c E`
  obtain ⟨c, hc⟩ := (mem_range_scalar_iff_commute_single (M := F * σ)).mpr
    fun i j _ => hcomm (single i j 1)
  have hσE : σ = c • E := by
    calc σ = E * (F * σ) := by rw [← Matrix.mul_assoc, hEF, Matrix.one_mul]
      _ = E * scalar ι c := by rw [hc]
      _ = c • E := by
        rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  -- 第四步：`tr σ = 1` 定出 `c = (tr E)⁻¹`
  have hc1 : c * trace E = 1 := by rw [← hσ, hσE, trace_smul, smul_eq_mul]
  rw [hσE, eq_inv_of_mul_eq_one_left hc1]

/-- **S2 逆向唯一**：跡為 1 且滿足 KMS 條件的 `σ` 必是 `gibbs H β`。
不需要 `H` Hermitian、不需要 `ι` 非空；`tr σ = 1` 不可省（K2 演習：`σ` 只定到純量倍）。 -/
theorem isKMS_unique {σ H : Matrix ι ι ℂ} {β : ℝ} (hσ : trace σ = 1) (hk : IsKMS σ H β) :
    σ = gibbs H β :=
  kms_core (exp_mul_exp_neg H β) (exp_neg_mul_exp H β) hk hσ

/-- **S2 刻畫**：`H` Hermitian、`ι` 非空時，`σ` 是跡為 1 的 KMS 態 ⇔ `σ = gibbs H β`。 -/
theorem isKMS_iff_eq_gibbs [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (σ : Matrix ι ι ℂ) (β : ℝ) : trace σ = 1 ∧ IsKMS σ H β ↔ σ = gibbs H β := by
  refine ⟨fun h => isKMS_unique h.1 h.2, fun h => ?_⟩
  rw [h]
  exact ⟨trace_gibbs hH β, gibbs_isKMS H β⟩

/-! ## 與 T2 接起來 -/

/-- Gibbs 態的轉置是 `Hᵀ` 的 Gibbs 態（`Matrix.exp_transpose`）。 -/
theorem gibbs_transpose (H : Matrix ι ι ℂ) (β : ℝ) : (gibbs H β)ᵀ = gibbs Hᵀ β := by
  rw [gibbs, gibbs, ← transpose_smul (-(β : ℂ)) H, Matrix.exp_transpose, trace_transpose,
    transpose_smul]

/-- **S2 × T2a**：TFD 的 A 側約化態是 `H` 的 KMS 態。 -/
theorem tfd_ptrB_isKMS {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    IsKMS (ptrB (tfdState hH β)) H β := by
  rw [ptrB_tfdState]
  exact gibbs_isKMS H β

/-- **S2 × T2b**：TFD 的 B 側約化態是 `Hᵀ` 的 KMS 態（不是 `H` 的；σ_y 下兩者不同，見 T2c）。 -/
theorem tfd_ptrA_isKMS {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    IsKMS (ptrA (tfdState hH β)) Hᵀ β := by
  rw [ptrA_tfdState, gibbs_transpose]
  exact gibbs_isKMS Hᵀ β

/-! ## 負控制：純量態不是 KMS 態 -/

/-- `diag(d) · E_{ij}(c) · diag(e) = E_{ij}(d_i c e_j)`。 -/
theorem diagonal_mul_single_mul_diagonal (d e : ι → ℂ) (i j : ι) (c : ℂ) :
    diagonal d * single i j c * diagonal e = single i j (d i * c * e j) := by
  ext k l
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · rw [h.1, h.2]
  · rw [mul_zero, zero_mul]

/-- **負控制（一般形）**：實對角 `H` 有兩個不同的固有值 `E i ≠ E j`、`β ≠ 0` 時，
任何非零純量態 `c • 1` 都**不**滿足 KMS 條件（`E i ≠ E j` 已蘊含 `i ≠ j`）。
見證：`a = E_{ij}`、`b = E_{ji}`。
所以 `IsKMS` 不是空條件；把 `nuStep` 換成恆等（K1 演習）時這條會變成假的。 -/
theorem negctrl_scalar_not_kms {c : ℂ} (hc : c ≠ 0) {E : ι → ℝ} {i j : ι} (hE : E i ≠ E j)
    {β : ℝ} (hβ : β ≠ 0) :
    ¬ IsKMS (c • (1 : Matrix ι ι ℂ)) (diagonal fun k => (E k : ℂ)) β := by
  intro h
  have h1 := h (single i j 1) (single j i 1)
  rw [nuStep, exp_neg_smul_diagonal, exp_smul_diagonal, diagonal_mul_single_mul_diagonal] at h1
  simp only [Matrix.smul_mul, one_mul, single_mul_single_same, trace_smul,
    trace_single_eq_same, smul_eq_mul, mul_one] at h1
  have h2 := mul_left_cancel₀ hc (h1.trans (mul_one c).symm)
  rw [← Complex.ofReal_mul, Complex.ofReal_eq_one, ← Real.exp_add, Real.exp_eq_one_iff] at h2
  have h3 : β * (E i - E j) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact hβ h4
  · exact hE (sub_eq_zero.mp h4)

/-- **負控制（CHAIN_DESIGN §5.2 S2 指定的實例）**：`H = diag(0, 1)`、`β ≠ 0` 時，
最大混合態 `(1/2) • 1` 不滿足 KMS 條件。 -/
theorem negctrl_maxMixed_not_kms {β : ℝ} (hβ : β ≠ 0) :
    ¬ IsKMS ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) H2 β :=
  negctrl_scalar_not_kms (by norm_num) (E := ![0, 1]) (i := 0) (j := 1) (by norm_num) hβ

end

end ErEpr
