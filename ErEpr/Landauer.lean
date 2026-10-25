import ErEpr.Modular

/-!
# ErEpr.Landauer：完整的 Landauer 原理（`docs/TRIANGLE.md` §5 的 T-d）

系統 `S`（指標 `ι`）處於任意態 `ρ_S`，熱庫 `R`（指標 `κ`）處於溫度 `1/β` 的 Gibbs 態
`γ = gibbs H β`。兩者一起做任意么正演化 `U`，終態 `ρ′ = U (ρ_S ⊗ γ) Uᴴ`，
系統的終態是 `ρ′_S = Tr_R ρ′`（`ptrB`），熱庫的終態是 `ρ′_R = Tr_S ρ′`（`ptrA`）。

* **Landauer**（`landauer`）：`S(ρ_S) − S(ρ′_S) ≤ β·(tr(ρ′_R H) − tr(γ H))`，
  即系統熵的減少不超過 `β` 乘熱庫吸收的熱。抹掉一個位元（熵少 `ln 2`）至少要放 `T ln 2` 的熱
  （`landauer_bit`）；熱庫不吸熱時系統的熵不能減少（`no_heatless_erasure`）。
* 證明（Reeb–Wolf 2014 的有限維路線）由四塊組成：
  1. 么正不變 `S(Uρ Uᴴ) = S(ρ)`（既有的 `vnEntropy_unitary_conj`）；
  2. **張量積可加** `S(ρ ⊗ σ) = S(ρ) + S(σ)`（`vnEntropy_kronecker`）：
     兩組固有分解的 Kronecker 積是 `ρ ⊗ σ` 的固有分解（`kronecker_spectral`），
     再用 `−xy log xy = y·(−x log x) + x·(−y log y)`；
  3. **次可加性** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`（`vnEntropy_subadditive`），見下；
  4. 熱庫那一半 `S(ρ′_R) − S(γ) ≤ β·ΔQ`（既有的 T-b `reservoir_entropy_le_beta_heat`）。
* **次可加性的證法**：相對熵 `D(ρ_AB ‖ τ_A ⊗ τ_B) ≥ 0`（既有的 `relEntropyOf_nonneg`）。
  它要求參考態滿秩，而邊際態可能不滿秩（抹除之後恰好如此）。所以參考態改用
  `τ_A = (1 − ε)ρ_A + ε/d`（`mixUnif`），與 `ρ_A` 共用固有基底，對所有 `ε ∈ (0, 1]` 都滿秩：
  * `τ_A ⊗ τ_B` 的模哈密頓量是 `K_A ⊗ 1 + 1 ⊗ K_B`（`modHamOf_kronecker`），
    配上部分跡的對偶刻畫，`tr(ρ_AB K)` 拆成兩個邊際各自的 `tr(ρ_A K_A) + tr(ρ_B K_B)`
    （`vnEntropy_le_marginal_cross`）；
  * 共用固有基底，所以 `tr(ρ_A K_A) = −Σ a_i log((1 − ε)a_i + ε/d)`（`trace_mul_modHamOf_of_eq`）：
    只是有限個初等函數的和。`a_i = 0` 的項恆為 0，`a_i > 0` 的項靠 `log` 的連續性收斂
    （`tendsto_mul_log_mixUnif`）。取 `ε = 1/(n+1) → 0` 得到次可加性。
  整個過程**不需要**固有值對矩陣的連續性（mathlib 沒有）。
* 見證與負控制：
  * `landauer_swap_witness`：交換系統與熱庫（`swapU`）時系統的熵**嚴格**減少、熱庫**嚴格**吸熱，
    所以定理不是空話；
  * `negctrl_landauer_not_unitary`：換成非么正的重置 `|0⟩⟨0| + |0⟩⟨1|`（`resetS`），
    不放熱就把最大混合態變成純態，不等式失敗：么正性不能拿掉；
  * `negctrl_subadditive_unnormalized`：跡不為 1 時次可加性可以失敗。

範圍（引用前請讀）：
* 這是有限維、熱庫起點恰為 Gibbs 態、系統與熱庫起點為乘積態的陳述。「熱」定義為熱庫的能量增量
  `tr(ρ′_R H) − tr(γ H)`；系統本身的哈密頓量與做功沒有出現在定理裡。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
* 自然單位 `k_B = 1`，熵以 nat 計（一個位元是 `ln 2`）。
-/

namespace ErEpr

open Matrix Filter Topology
open scoped Kronecker ComplexOrder Real

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## 部分跡 A 側的補件 -/

omit [DecidableEq κ] in
/-- 對偶刻畫（A 側）：`ptrA` 是 `B ↦ 1 ⊗ B` 對跡配對的伴隨。 -/
theorem trace_ptrA_mul (X : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix κ κ ℂ) :
    trace (ptrA X * B) = trace (X * ((1 : Matrix ι ι ℂ) ⊗ₖ B)) := by
  have hR : ∀ (i : ι) (k : κ),
      ∑ j : ι, ∑ l : κ, X (i, k) (j, l) * ((1 : Matrix ι ι ℂ) j i * B l k) =
        ∑ l : κ, X (i, k) (i, l) * B l k := by
    intro i k
    rw [Fintype.sum_eq_single i]
    · simp
    · intro j hj
      simp [one_apply_ne hj]
  simp only [trace, diag_apply, mul_apply, ptrA_apply, kroneckerMap_apply, Fintype.sum_prod_type,
    hR, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- 乘積態（A 側）：`Tr_A (A ⊗ B) = (tr A) · B`。 -/
theorem ptrA_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    ptrA (A ⊗ₖ B) = trace A • B := by
  ext k l
  simp only [ptrA_apply, kroneckerMap_apply, trace, diag_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]

omit [DecidableEq ι] [DecidableEq κ] in
/-- 保跡（A 側）。 -/
theorem trace_ptrA (X : Matrix (ι × κ) (ι × κ) ℂ) : trace (ptrA X) = trace X := by
  simp only [trace, diag_apply, ptrA_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- 保半正定（A 側）。 -/
theorem ptrA_posSemidef {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) : (ptrA X).PosSemidef :=
  ptrB_posSemidef (hX.submatrix _)

/-! ## Kronecker 積與么正矩陣 -/

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem star_kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) : star (U ⊗ₖ V) = star U ⊗ₖ star V := by
  simp only [star_eq_conjTranspose, conjTranspose_kronecker]

theorem kronecker_star_mul {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ} (hU : star U * U = 1)
    (hV : star V * V = 1) : star (U ⊗ₖ V) * (U ⊗ₖ V) = 1 := by
  rw [star_kronecker, ← mul_kronecker_mul, hU, hV, one_kronecker_one]

theorem kronecker_mul_star {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ} (hU : U * star U = 1)
    (hV : V * star V = 1) : (U ⊗ₖ V) * star (U ⊗ₖ V) = 1 := by
  rw [star_kronecker, ← mul_kronecker_mul, hU, hV, one_kronecker_one]

/-- 兩個么正矩陣的 Kronecker 積仍是么正矩陣。 -/
def kronU (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ)) :
    unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Unitary.mem_iff.mpr
      ⟨kronecker_star_mul (Unitary.coe_star_mul_self U) (Unitary.coe_star_mul_self V),
        kronecker_mul_star (Unitary.coe_mul_star_self U) (Unitary.coe_mul_star_self V)⟩⟩

theorem coe_kronU (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ)) :
    (kronU U V : Matrix (ι × κ) (ι × κ) ℂ) = (U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ) := rfl

/-! ## 張量積可加 -/

/-- 兩組固有分解的 Kronecker 積是 `ρ ⊗ σ` 的固有分解。 -/
theorem kronecker_spectral {ρ : Matrix ι ι ℂ} {σ : Matrix κ κ ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    ρ ⊗ₖ σ = (eigU hρ ⊗ₖ eigU hσ) *
      diagonal (fun p : ι × κ => ((hρ.eigenvalues p.1 * hσ.eigenvalues p.2 : ℝ) : ℂ)) *
        star (eigU hρ ⊗ₖ eigU hσ) := by
  have hd : diagonal (fun p : ι × κ => ((hρ.eigenvalues p.1 * hσ.eigenvalues p.2 : ℝ) : ℂ)) =
      diagonal (fun i => (hρ.eigenvalues i : ℂ)) ⊗ₖ diagonal (fun k => (hσ.eigenvalues k : ℂ)) := by
    rw [diagonal_kronecker_diagonal]
    congr 1
    funext p
    exact Complex.ofReal_mul _ _
  conv_lhs => rw [eigU_spectral hρ, eigU_spectral hσ]
  rw [hd, star_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

/-- **張量積可加**：`S(ρ ⊗ σ) = S(ρ) + S(σ)`（兩者 Hermitian、跡為 1）。 -/
theorem vnEntropy_kronecker {ρ : Matrix ι ι ℂ} {σ : Matrix κ κ ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (htrρ : trace ρ = 1) (htrσ : trace σ = 1) :
    vnEntropy (ρ ⊗ₖ σ) = vnEntropy ρ + vnEntropy σ := by
  rw [kronecker_spectral hρ hσ,
    vnEntropy_unitary_conj _ _ (kronecker_star_mul (eigU_star_mul hρ) (eigU_star_mul hσ)),
    vnEntropy_diagonal, vnEntropy_eq_sum_eigenvalues hρ, vnEntropy_eq_sum_eigenvalues hσ,
    Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_eigenvalues_of_trace_eq_one hρ htrρ, sum_eigenvalues_of_trace_eq_one hσ htrσ, one_mul]

/-! ## 次可加性：乘積參考態的模哈密頓量 -/

/-- 乘積參考態 `τ_A ⊗ τ_B` 的模哈密頓量是 `K_A ⊗ 1 + 1 ⊗ K_B`。 -/
theorem modHamOf_kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) (hU : U * star U = 1)
    (hV : V * star V = 1) {x : ι → ℝ} {y : κ → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ k, 0 < y k) :
    modHamOf (U ⊗ₖ V) (fun p => x p.1 * y p.2) =
      modHamOf U x ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ modHamOf V y := by
  have hd : diagonal (fun p : ι × κ => ((-Real.log (x p.1 * y p.2) : ℝ) : ℂ)) =
      diagonal (fun i => ((-Real.log (x i) : ℝ) : ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) +
        (1 : Matrix ι ι ℂ) ⊗ₖ diagonal (fun k => ((-Real.log (y k) : ℝ) : ℂ)) := by
    rw [← diagonal_one, ← diagonal_one, diagonal_kronecker_diagonal, diagonal_kronecker_diagonal,
      diagonal_add]
    congr 1
    funext p
    rw [Real.log_mul (hx p.1).ne' (hy p.2).ne']
    push_cast
    ring
  simp only [modHamOf]
  rw [hd, star_kronecker, Matrix.mul_add, Matrix.add_mul]
  simp only [← mul_kronecker_mul, Matrix.mul_one, hU, hV]

/-- 與 `σ` 共用固有基底時：`tr(σ K) = −Σ a_i log x_i`，`σ = U·diag(a)·Uᴴ`、`K = modHamOf U x`。 -/
theorem trace_mul_modHamOf_of_eq {σ : Matrix ι ι ℂ} (U : Matrix ι ι ℂ) (hU : star U * U = 1)
    (a x : ι → ℝ) (hσ : σ = U * diagonal (fun i => (a i : ℂ)) * star U) :
    (trace (σ * modHamOf U x)).re = -∑ i, a i * Real.log (x i) := by
  have h : σ * modHamOf U x =
      U * (diagonal (fun i => (a i : ℂ)) * diagonal (fun i => ((-Real.log (x i) : ℝ) : ℂ))) *
        star U := by
    rw [hσ, modHamOf]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
  rw [h, trace_mul_cycle, hU, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **相對熵拆成兩個邊際**：任何滿秩乘積參考態 `(U·diag x·Uᴴ) ⊗ (V·diag y·Vᴴ)`，
`S(ρ) ≤ tr(ρ_A K_A) + tr(ρ_B K_B)`。 -/
theorem vnEntropy_le_marginal_cross (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ))
    {x : ι → ℝ} {y : κ → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ k, 0 < y k)
    (hx1 : ∑ i, x i = 1) (hy1 : ∑ k, y k = 1)
    {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy ρ ≤ (trace (ptrB ρ * modHamOf (U : Matrix ι ι ℂ) x)).re +
      (trace (ptrA ρ * modHamOf (V : Matrix κ κ ℂ) y)).re := by
  have hq : ∀ p : ι × κ, 0 < x p.1 * y p.2 := fun p => mul_pos (hx p.1) (hy p.2)
  have hq1 : ∑ p : ι × κ, x p.1 * y p.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hy1, mul_one, hx1]
  have h := relEntropyOf_nonneg (kronU U V) hq hq1 hρ htr
  rw [relEntropyOf, coe_kronU, modHamOf_kronecker _ _ (Unitary.coe_mul_star_self U)
    (Unitary.coe_mul_star_self V) hx hy, Matrix.mul_add, trace_add, Complex.add_re,
    ← trace_ptrB_mul, ← trace_ptrA_mul] at h
  linarith

/-! ## 次可加性：往均勻分佈混一點，再取極限 -/

/-- 往均勻分佈混一點：`(1 − ε)·a_i + ε/d`。 -/
def mixUnif (ε : ℝ) (a : ι → ℝ) (i : ι) : ℝ := (1 - ε) * a i + ε / Fintype.card ι

omit [DecidableEq ι] in
theorem mixUnif_pos [Nonempty ι] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (i : ι) : 0 < mixUnif ε a i := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : 0 ≤ (1 - ε) * a i := mul_nonneg (by linarith) (ha i)
  have h2 : 0 < ε / Fintype.card ι := div_pos hε hd
  rw [mixUnif]
  linarith

omit [DecidableEq ι] in
theorem sum_mixUnif [Nonempty ι] (ε : ℝ) {a : ι → ℝ} (ha1 : ∑ i, a i = 1) :
    ∑ i, mixUnif ε a i = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [mixUnif, Finset.sum_add_distrib, ← Finset.mul_sum, ha1, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel₀ ε hd]
  ring

/-- 逐項的極限：`a ≥ 0` 時 `a·log((1 − ε)a + ε/c) → a log a`（`ε → 0`）。
`a = 0` 時整項恆為 0；`a > 0` 時靠 `log` 在 `a` 的連續性。 -/
theorem tendsto_mul_log_mixUnif {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    Tendsto (fun ε : ℝ => a * Real.log ((1 - ε) * a + ε / c)) (𝓝 0) (𝓝 (a * Real.log a)) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul]
    exact tendsto_const_nhds
  · have hc : ContinuousAt (fun ε : ℝ => (1 - ε) * a + ε / c) 0 := by fun_prop
    have h0 : (1 - (0 : ℝ)) * a + 0 / c ≠ 0 := by
      rw [sub_zero, one_mul, zero_div, add_zero]
      exact ha.ne'
    have h : ContinuousAt (fun ε : ℝ => a * Real.log ((1 - ε) * a + ε / c)) 0 :=
      continuousAt_const.mul (hc.log h0)
    simpa using h.tendsto

/-- 次可加性的核心：邊際態寫成 `U·diag(a)·Uᴴ`、`V·diag(b)·Vᴴ`（`a`、`b` 可以有 0），
`S(ρ) ≤ Σ −a_i log a_i + Σ −b_k log b_k`。 -/
theorem vnEntropy_le_of_marginal_spectral {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ))
    {a : ι → ℝ} {b : κ → ℝ} (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ k, 0 ≤ b k)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ k, b k = 1)
    (hA : ptrB ρ = (U : Matrix ι ι ℂ) * diagonal (fun i => (a i : ℂ)) * star (U : Matrix ι ι ℂ))
    (hB : ptrA ρ = (V : Matrix κ κ ℂ) * diagonal (fun k => (b k : ℂ)) * star (V : Matrix κ κ ℂ)) :
    vnEntropy ρ ≤ ∑ i, Real.negMulLog (a i) + ∑ k, Real.negMulLog (b k) := by
  have hι : Nonempty ι := nonempty_of_trace_eq_one (by rw [trace_ptrB, htr] : trace (ptrB ρ) = 1)
  have hκ : Nonempty κ := nonempty_of_trace_eq_one (by rw [trace_ptrA, htr] : trace (ptrA ρ) = 1)
  have hbound : ∀ n : ℕ, vnEntropy ρ ≤
      -∑ i, a i * Real.log (mixUnif (1 / ((n : ℝ) + 1)) a i) -
        ∑ k, b k * Real.log (mixUnif (1 / ((n : ℝ) + 1)) b k) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h := vnEntropy_le_marginal_cross U V (mixUnif_pos hε hε1 ha0) (mixUnif_pos hε hε1 hb0)
      (sum_mixUnif _ ha1) (sum_mixUnif _ hb1) hρ htr
    rw [trace_mul_modHamOf_of_eq (U : Matrix ι ι ℂ) (Unitary.coe_star_mul_self U) a _ hA,
      trace_mul_modHamOf_of_eq (V : Matrix κ κ ℂ) (Unitary.coe_star_mul_self V) b _ hB] at h
    linarith
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => ∑ i, a i * Real.log (mixUnif (1 / ((n : ℝ) + 1)) a i)) atTop
      (𝓝 (∑ i, a i * Real.log (a i))) :=
    tendsto_finsetSum _ fun i _ =>
      (tendsto_mul_log_mixUnif (ha0 i) (Fintype.card ι : ℝ)).comp h0
  have h2 : Tendsto (fun n : ℕ => ∑ k, b k * Real.log (mixUnif (1 / ((n : ℝ) + 1)) b k)) atTop
      (𝓝 (∑ k, b k * Real.log (b k))) :=
    tendsto_finsetSum _ fun k _ =>
      (tendsto_mul_log_mixUnif (hb0 k) (Fintype.card κ : ℝ)).comp h0
  have h := ge_of_tendsto (h1.neg.sub h2) (Eventually.of_forall hbound)
  have e : -∑ i, a i * Real.log (a i) - ∑ k, b k * Real.log (b k) =
      ∑ i, Real.negMulLog (a i) + ∑ k, Real.negMulLog (b k) := by
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    ring
  linarith

/-- **次可加性** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`：任何密度矩陣，邊際態不必滿秩。 -/
theorem vnEntropy_subadditive {ρ : Matrix (ι × κ) (ι × κ) ℂ} (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) : vnEntropy ρ ≤ vnEntropy (ptrB ρ) + vnEntropy (ptrA ρ) := by
  have hA := ptrB_posSemidef hρ
  have hB := ptrA_posSemidef hρ
  have htrA : trace (ptrB ρ) = 1 := by rw [trace_ptrB, htr]
  have htrB : trace (ptrA ρ) = 1 := by rw [trace_ptrA, htr]
  rw [vnEntropy_eq_sum_eigenvalues hA.1, vnEntropy_eq_sum_eigenvalues hB.1]
  exact vnEntropy_le_of_marginal_spectral hρ htr hA.1.eigenvectorUnitary hB.1.eigenvectorUnitary
    hA.eigenvalues_nonneg hB.eigenvalues_nonneg (sum_eigenvalues_of_trace_eq_one hA.1 htrA)
    (sum_eigenvalues_of_trace_eq_one hB.1 htrB) (eigU_spectral hA.1) (eigU_spectral hB.1)

/-! ## 完整的 Landauer -/

/-- **Landauer**：系統 `ρ_S` 與 Gibbs 熱庫 `γ = gibbs H β` 一起做么正演化 `U`，
`S(ρ_S) − S(ρ′_S) ≤ β·(tr(ρ′_R H) − tr(γ H))`。 -/
theorem landauer [Nonempty κ] {ρS : Matrix ι ι ℂ} (hρS : ρS.PosSemidef) (htrS : trace ρS = 1)
    {H : Matrix κ κ ℂ} (hH : H.IsHermitian) (β : ℝ) {U : Matrix (ι × κ) (ι × κ) ℂ}
    (hU : star U * U = 1) :
    vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H β) * star U)) ≤
      β * ((trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re -
        (trace (gibbs H β * H)).re) := by
  have hγ := gibbs_posSemidef hH β
  have htrγ := trace_gibbs hH β
  have hρ' : (U * (ρS ⊗ₖ gibbs H β) * star U).PosSemidef := by
    rw [star_eq_conjTranspose]
    exact (hρS.kronecker hγ).mul_mul_conjTranspose_same U
  have htr' : trace (U * (ρS ⊗ₖ gibbs H β) * star U) = 1 := by
    rw [trace_mul_cycle, hU, Matrix.one_mul, trace_kronecker, htrS, htrγ, mul_one]
  have hS : vnEntropy (U * (ρS ⊗ₖ gibbs H β) * star U) = vnEntropy ρS + vnEntropy (gibbs H β) := by
    rw [vnEntropy_unitary_conj _ _ hU, vnEntropy_kronecker hρS.1 hγ.1 htrS htrγ]
  have hsub := vnEntropy_subadditive hρ' htr'
  have hres := reservoir_entropy_le_beta_heat hH β (ptrA_posSemidef hρ')
    (by rw [trace_ptrA, htr'])
  linarith

/-- **一個位元**：`β > 0`、系統熵至少少了 `ln 2` 時，熱庫至少吸收 `ln 2 / β = T ln 2` 的熱。 -/
theorem landauer_bit [Nonempty κ] {ρS : Matrix ι ι ℂ} (hρS : ρS.PosSemidef) (htrS : trace ρS = 1)
    {H : Matrix κ κ ℂ} (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β) {U : Matrix (ι × κ) (ι × κ) ℂ}
    (hU : star U * U = 1)
    (hbit : Real.log 2 ≤ vnEntropy ρS - vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H β) * star U))) :
    Real.log 2 / β ≤ (trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re -
      (trace (gibbs H β * H)).re := by
  rw [div_le_iff₀ hβ]
  have := landauer hρS htrS hH β hU
  linarith

/-- **不放熱就不能抹除**：`β ≥ 0`、熱庫沒有吸熱時，系統的熵不會減少。 -/
theorem no_heatless_erasure [Nonempty κ] {ρS : Matrix ι ι ℂ} (hρS : ρS.PosSemidef)
    (htrS : trace ρS = 1) {H : Matrix κ κ ℂ} (hH : H.IsHermitian) {β : ℝ} (hβ : 0 ≤ β)
    {U : Matrix (ι × κ) (ι × κ) ℂ} (hU : star U * U = 1)
    (hQ : (trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re ≤ (trace (gibbs H β * H)).re) :
    vnEntropy ρS ≤ vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs H β) * star U)) := by
  have h := landauer hρS htrS hH β hU
  have : β * ((trace (ptrA (U * (ρS ⊗ₖ gibbs H β) * star U) * H)).re -
      (trace (gibbs H β * H)).re) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  linarith

/-! ## 見證：交換系統與熱庫 -/

section Swap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 交換兩個 `n` 維因子的置換矩陣。 -/
def swapU (n : Type*) [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => if p.swap = q then 1 else 0

theorem swapU_mul_apply (M : Matrix (n × n) (n × n) ℂ) (p q : n × n) :
    (swapU n * M) p q = M p.swap q := by
  simp [swapU, Matrix.mul_apply]

theorem mul_swapU_apply (M : Matrix (n × n) (n × n) ℂ) (p q : n × n) :
    (M * swapU n) p q = M p q.swap := by
  simp [swapU, Matrix.mul_apply, Prod.swap_eq_iff_eq_swap]

omit [Fintype n] in
theorem star_swapU : star (swapU n) = swapU n := by
  ext p q
  rw [Matrix.star_apply]
  simp only [swapU, Matrix.of_apply]
  by_cases h : p.swap = q
  · have h' : q.swap = p := by rw [← h, Prod.swap_swap]
    rw [if_pos h, if_pos h', star_one]
  · have h' : ¬ q.swap = p := fun h' => h (by rw [← h', Prod.swap_swap])
    rw [if_neg h, if_neg h', star_zero]

theorem swapU_star_mul : star (swapU n) * swapU n = 1 := by
  rw [star_swapU]
  ext p q
  rw [swapU_mul_apply, one_apply]
  simp [swapU]

/-- 交換：`swap (A ⊗ B) swapᴴ = B ⊗ A`。 -/
theorem swapU_conj_kronecker (A B : Matrix n n ℂ) :
    swapU n * (A ⊗ₖ B) * star (swapU n) = B ⊗ₖ A := by
  rw [star_swapU]
  ext p q
  simp only [mul_swapU_apply, swapU_mul_apply, kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

end Swap

/-- 一個 qubit 的最大混合態 `diag(1/2, 1/2)`。 -/
def mix2 : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => ((![1 / 2, 1 / 2] i : ℝ) : ℂ)

theorem mix2_posSemidef : mix2.PosSemidef :=
  posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (by fin_cases i <;> norm_num)

theorem trace_mix2 : trace mix2 = 1 := by
  rw [mix2, trace_diagonal, Fin.sum_univ_two]
  norm_num

theorem vnEntropy_mix2 : vnEntropy mix2 = Real.log 2 := by
  rw [mix2, vnEntropy_diagonal, Fin.sum_univ_two]
  simp [Real.negMulLog]
  ring

theorem vnEntropy_ket0Proj : vnEntropy ket0Proj = 0 := by
  rw [ket0Proj, vnEntropy_diagonal, Fin.sum_univ_two]
  simp

/-- `S(diag(2/3, 1/3)) = log 3 − (2/3) log 2 < log 2`（等價於 `27 < 32`）。 -/
theorem vnEntropy_gibbs_H2_log2_lt : vnEntropy (gibbs H2 (Real.log 2)) < Real.log 2 := by
  rw [gibbs_H2_log2, vnEntropy_diagonal, Fin.sum_univ_two]
  have h23 : Real.log (2 / 3) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  have h13 : Real.log (1 / 3) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have h27 : 3 * Real.log 3 < 5 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 27) (by norm_num : (27 : ℝ) < 32)
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow,
      Real.log_pow] at h
    push_cast at h
    linarith
  simp only [Real.negMulLog, Matrix.cons_val_zero, Matrix.cons_val_one, h23, h13]
  linarith

/-- **見證**：最大混合 qubit 與 `β = ln 2` 的 Gibbs 熱庫（`H = diag(0, 1)`）交換之後，
系統的熵**嚴格**減少，熱庫**嚴格**吸熱（`1/2 − 1/3 = 1/6`）。所以 `landauer` 不是空話。 -/
theorem landauer_swap_witness :
    vnEntropy (ptrB (swapU (Fin 2) * (mix2 ⊗ₖ gibbs H2 (Real.log 2)) * star (swapU (Fin 2)))) <
        vnEntropy mix2 ∧
      0 < (trace (ptrA (swapU (Fin 2) * (mix2 ⊗ₖ gibbs H2 (Real.log 2)) *
          star (swapU (Fin 2))) * H2)).re - (trace (gibbs H2 (Real.log 2) * H2)).re := by
  rw [swapU_conj_kronecker, ptrB_kronecker, ptrA_kronecker, trace_mix2,
    trace_gibbs H2_isHermitian, one_smul, one_smul, vnEntropy_mix2]
  refine ⟨vnEntropy_gibbs_H2_log2_lt, ?_⟩
  rw [gibbs_H2_log2]
  norm_num [mix2, H2, diagonal_mul_diagonal, trace_diagonal, Fin.sum_univ_two]

/-! ## 負控制 -/

/-- 重置 `|0⟩⟨0| + |0⟩⟨1|`：把 `|0⟩`、`|1⟩` 都送到 `|0⟩`。 -/
def resetS : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]

/-- 重置不是么正矩陣。 -/
theorem resetS_not_unitary : star resetS * resetS ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [resetS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h01

theorem resetS_conj_mix2 : resetS * mix2 * star resetS = ket0Proj := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  fin_cases i <;> fin_cases j <;> norm_num [resetS, mix2, ket0Proj]

/-- **負控制**：么正性不能拿掉。把系統做非么正的重置（熱庫不動），
最大混合態變成純態、熵少了 `ln 2`，熱庫卻完全沒有吸熱。 -/
theorem negctrl_landauer_not_unitary [Nonempty κ] {H : Matrix κ κ ℂ} (hH : H.IsHermitian) (β : ℝ) :
    ¬ (vnEntropy mix2 - vnEntropy (ptrB ((resetS ⊗ₖ (1 : Matrix κ κ ℂ)) *
          (mix2 ⊗ₖ gibbs H β) * star (resetS ⊗ₖ (1 : Matrix κ κ ℂ)))) ≤
        β * ((trace (ptrA ((resetS ⊗ₖ (1 : Matrix κ κ ℂ)) * (mix2 ⊗ₖ gibbs H β) *
          star (resetS ⊗ₖ (1 : Matrix κ κ ℂ))) * H)).re - (trace (gibbs H β * H)).re)) := by
  have hJ : (resetS ⊗ₖ (1 : Matrix κ κ ℂ)) * (mix2 ⊗ₖ gibbs H β) *
      star (resetS ⊗ₖ (1 : Matrix κ κ ℂ)) = ket0Proj ⊗ₖ gibbs H β := by
    rw [star_kronecker, star_one, ← mul_kronecker_mul, ← mul_kronecker_mul, resetS_conj_mix2,
      Matrix.one_mul, Matrix.mul_one]
  rw [hJ, ptrB_kronecker, ptrA_kronecker, trace_gibbs hH β, trace_ket0Proj, one_smul, one_smul,
    vnEntropy_mix2, vnEntropy_ket0Proj, sub_zero, sub_self, mul_zero, not_le]
  exact Real.log_pos one_lt_two

/-- **負控制**：跡為 1 不能拿掉。`ρ = 2·1`（一維 ⊗ 一維）時 `S(ρ) = −2 log 2`，
兩個邊際各是 `−2 log 2`，和是 `−4 log 2 < S(ρ)`。 -/
theorem negctrl_subadditive_unnormalized :
    ¬ (vnEntropy (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)) ≤
        vnEntropy (ptrB (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))) +
          vnEntropy (ptrA (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)))) := by
  have hB : ptrB (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)) =
      ((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [ptrB_smul, ← one_kronecker_one, ptrB_kronecker, trace_one, Fintype.card_fin, Nat.cast_one,
      one_smul]
  have hA : ptrA (((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)) =
      ((2 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [ptrA_smul, ← one_kronecker_one, ptrA_kronecker, trace_one, Fintype.card_fin, Nat.cast_one,
      one_smul]
  rw [hB, hA, vnEntropy_smul_one, vnEntropy_smul_one]
  simp only [Fintype.card_prod, Fintype.card_fin, mul_one, Nat.cast_one, one_mul, not_le]
  have h : Real.negMulLog 2 < 0 := by
    rw [Real.negMulLog]
    have := Real.log_pos one_lt_two
    nlinarith
  linarith

end

end ErEpr
