import ErEpr.Modular

/-!
# ErEpr.FirstLaw：糾纏第一定律（對易情形）

參考態 `ρ₀ = diag(q)`（`q > 0`、`Σq = 1`），模哈密頓量 `K = −log ρ₀ = diag(−log q)`
（`modHamOf 1 q`）。沿對角路徑 `ρ(t) = diag(q + t·v)`（`diagPath`），`Σv = 0` 保持跡為 1：

* **糾纏第一定律**（`entanglement_first_law_diag`）：`δS = δ⟨K⟩`，即
  `d/dt S(ρ(t))|₀ = d/dt tr(ρ(t)K)|₀ = Σ v_i (−log q_i)`。
  直接微分：`hasDerivAt_entropy_diagPath`（`δS = Σ v_i (−log q_i − 1)`，其中 `−1` 那項因 `Σv = 0` 消失）
  與 `hasDerivAt_modEnergy_diagPath`（`δ⟨K⟩` 對任何參考 `r` 都算得出來）。
* **第二條路（互驗）**（`first_law_of_relEntropy_min`）：不算導數的值，只用 T-c 的
  「相對熵 ≥ 0、在 `ρ₀` 為 0」：`t = 0` 是 `D(ρ(t)‖ρ₀)` 的局部極小，所以只要兩邊可微，
  導數就相等。一階的等號是二階不等式（極小值）的影子。
* **一階相等、二階嚴格**（`relEntropy_diagPath_pos`）：`v ≠ 0`、`t ≠ 0` 時 `D > 0`，
  所以第一定律只到一階。
* **負控制**（`negctrl_first_law_wrong_reference`）：`K` 必須是**同一個**參考態的模哈密頓量。
  `q = (1/2, 1/2)`、`v = (1, −1)` 時 `δS = 0`，換成 `r = (2/3, 1/3)` 的模哈密頓量則 `δ⟨K_r⟩ = −ln 2`。

範圍（引用前請讀）：
* 只做對易（對角）情形：路徑與參考態同時對角化。一般（不對易）擾動需要熵沿矩陣路徑的導數
  （固有值的一階微擾），本檔沒有做。
* 物理上這是「從糾纏推出重力」那條路（Jacobson 1995；Lashkari–McDermott–Van Raamsdonk、
  Faulkner 等 2014）的輸入之一；另一半輸入是「面積 = 熵」（RT 公式）與幾何，本庫沒有，
  所以這裡**沒有**任何關於 Einstein 方程的陳述。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder Real Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 對角路徑 `ρ(t) = diag(q + t·v)`。 -/
def diagPath (q v : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  diagonal fun i => ((q i + t * v i : ℝ) : ℂ)

/-- 路徑上的熵就是 Shannon 熵。 -/
theorem vnEntropy_diagPath (q v : ι → ℝ) (t : ℝ) :
    vnEntropy (diagPath q v t) = ∑ i, Real.negMulLog (q i + t * v i) :=
  vnEntropy_diagonal _

/-- 路徑上 `K_r = −log diag(r)` 的期望值。 -/
theorem modEnergy_diagPath (q v r : ι → ℝ) (t : ℝ) :
    (trace (diagPath q v t * modHamOf 1 r)).re = ∑ i, (q i + t * v i) * -Real.log (r i) := by
  rw [diagPath, modHamOf, Matrix.one_mul, star_one, Matrix.mul_one, diagonal_mul_diagonal,
    trace_diagonal, Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

theorem trace_diagPath {q : ι → ℝ} (hq1 : ∑ i, q i = 1) {v : ι → ℝ} (hv : ∑ i, v i = 0)
    (t : ℝ) : trace (diagPath q v t) = 1 := by
  rw [diagPath, trace_diagonal, ← Complex.ofReal_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    hq1, hv, mul_zero, add_zero, Complex.ofReal_one]

omit [Fintype ι] in
theorem diagPath_posSemidef {q v : ι → ℝ} {t : ℝ} (h : ∀ i, 0 ≤ q i + t * v i) :
    (diagPath q v t).PosSemidef :=
  posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (h i)

/-! ## 直接微分 -/

/-- **δS**：`q > 0` 時 `d/dt S(ρ(t))|₀ = Σ v_i (−log q_i − 1)`。 -/
theorem hasDerivAt_entropy_diagPath {q : ι → ℝ} (hq : ∀ i, 0 < q i) (v : ι → ℝ) :
    HasDerivAt (fun t => vnEntropy (diagPath q v t)) (∑ i, v i * (-Real.log (q i) - 1)) 0 := by
  have h : (fun t => vnEntropy (diagPath q v t)) =
      fun t => ∑ i, Real.negMulLog (q i + t * v i) := funext (vnEntropy_diagPath q v)
  rw [h]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hin : HasDerivAt (fun t : ℝ => q i + t * v i) (v i) 0 :=
    (hasDerivAt_mul_const (v i)).const_add (q i)
  have hout : HasDerivAt Real.negMulLog (-Real.log (q i + 0 * v i) - 1) (q i + 0 * v i) :=
    Real.hasDerivAt_negMulLog (by simpa using (hq i).ne')
  refine (hout.comp 0 hin).congr_deriv ?_
  rw [zero_mul, add_zero]
  ring

/-- **δ⟨K_r⟩**：`d/dt tr(ρ(t) K_r)|₀ = Σ v_i (−log r_i)`（對任何參考 `r`）。 -/
theorem hasDerivAt_modEnergy_diagPath (q v r : ι → ℝ) :
    HasDerivAt (fun t => (trace (diagPath q v t * modHamOf 1 r)).re)
      (∑ i, v i * -Real.log (r i)) 0 := by
  have h : (fun t => (trace (diagPath q v t * modHamOf 1 r)).re) =
      fun t => ∑ i, (q i + t * v i) * -Real.log (r i) := funext (modEnergy_diagPath q v r)
  rw [h]
  exact HasDerivAt.fun_sum fun i _ =>
    ((hasDerivAt_mul_const (v i)).const_add (q i)).mul_const (-Real.log (r i))

/-- **糾纏第一定律（對易情形）**：`q > 0`、`Σv = 0` ⇒ `δS = δ⟨K⟩`，`K = −log diag(q)`。 -/
theorem entanglement_first_law_diag {q : ι → ℝ} (hq : ∀ i, 0 < q i) {v : ι → ℝ}
    (hv : ∑ i, v i = 0) :
    deriv (fun t => vnEntropy (diagPath q v t)) 0 =
      deriv (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) 0 := by
  rw [(hasDerivAt_entropy_diagPath hq v).deriv, (hasDerivAt_modEnergy_diagPath q v q).deriv]
  have h : ∑ i, v i * (-Real.log (q i) - 1) = ∑ i, v i * -Real.log (q i) - ∑ i, v i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, hv, sub_zero]

/-! ## 第二條路：極小值的影子 -/

omit [DecidableEq ι] in
/-- 小 `t` 時路徑上的機率都是正的。 -/
theorem eventually_diagPath_pos {q : ι → ℝ} (hq : ∀ i, 0 < q i) (v : ι → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < q i + t * v i := by
  rw [Filter.eventually_all]
  intro i
  have hc : ContinuousAt (fun t : ℝ => q i + t * v i) 0 :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
  exact continuousAt_const.eventually_lt hc (by simpa using hq i)

/-- **第二條路（互驗）**：只用 T-c 的「相對熵 ≥ 0、在 `ρ₀` 為 0」，不算導數的值：
只要兩邊在 0 可微，`δS = δ⟨K⟩`。 -/
theorem first_law_of_relEntropy_min {q : ι → ℝ} (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    {v : ι → ℝ} (hv : ∑ i, v i = 0) {S' K' : ℝ}
    (hS : HasDerivAt (fun t => vnEntropy (diagPath q v t)) S' 0)
    (hK : HasDerivAt (fun t => (trace (diagPath q v t * modHamOf 1 q)).re) K' 0) :
    S' = K' := by
  have h0 : relEntropyOf 1 q (diagPath q v 0) = 0 := by
    have hd : diagPath q v 0 = diagonal fun i => (q i : ℂ) := by
      rw [diagPath]
      congr 1
      funext i
      simp
    rw [hd, relEntropyOf_diagonal]
    simp
  have hmin : IsLocalMin (fun t => relEntropyOf 1 q (diagPath q v t)) 0 := by
    filter_upwards [eventually_diagPath_pos hq v] with t ht
    show relEntropyOf 1 q (diagPath q v 0) ≤ relEntropyOf 1 q (diagPath q v t)
    rw [h0]
    exact relEntropyOf_nonneg (1 : unitary (Matrix ι ι ℂ)) hq hq1
      (diagPath_posSemidef fun i => (ht i).le) (trace_diagPath hq1 hv t)
  have hD : HasDerivAt (fun t => relEntropyOf 1 q (diagPath q v t)) (K' - S') 0 := hK.sub hS
  have := hmin.hasDerivAt_eq_zero hD
  linarith

/-- **一階相等、二階嚴格**：`v ≠ 0`、`t ≠ 0`、路徑上非負時 `D(ρ(t)‖ρ₀) > 0`。 -/
theorem relEntropy_diagPath_pos {q : ι → ℝ} (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    {v : ι → ℝ} (hv : ∑ i, v i = 0) (hv0 : v ≠ 0) {t : ℝ} (ht0 : t ≠ 0)
    (ht : ∀ i, 0 ≤ q i + t * v i) :
    0 < relEntropyOf 1 q (diagPath q v t) := by
  have hρ : diagonal (fun i => (q i : ℂ)) =
      ((1 : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) * diagonal (fun j => (q j : ℂ)) *
        star ((1 : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) := by
    simp
  refine lt_of_le_of_ne (relEntropyOf_nonneg 1 hq hq1 (diagPath_posSemidef ht)
    (trace_diagPath hq1 hv t)) ?_
  intro h
  have heq := (relEntropyOf_eq_zero_iff 1 hρ hq hq1 (diagPath_posSemidef ht)
    (trace_diagPath hq1 hv t)).1 h.symm
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  have hii := congrFun (congrFun heq i) i
  rw [diagPath, diagonal_apply_eq, diagonal_apply_eq] at hii
  have h2 : t * v i = 0 := by
    have := Complex.ofReal_injective hii
    linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact ht0 h3
  · exact hi h3

/-! ## 負控制 -/

/-- **負控制**：`K` 必須是同一個參考態的模哈密頓量。`q = (1/2, 1/2)`、`v = (1, −1)`：
`δS = 0`，但 `r = (2/3, 1/3)` 的模哈密頓量給 `δ⟨K_r⟩ = −ln 2`。 -/
theorem negctrl_first_law_wrong_reference :
    deriv (fun t => vnEntropy (diagPath ![1 / 2, 1 / 2] ![1, -1] t)) 0 ≠
      deriv (fun t => (trace (diagPath ![1 / 2, 1 / 2] ![1, -1] t *
        modHamOf 1 ![2 / 3, 1 / 3])).re) 0 := by
  have hq : ∀ i, (0 : ℝ) < ![1 / 2, 1 / 2] i := by
    intro i
    fin_cases i <;> norm_num
  have hL : ∑ i, ![(1 : ℝ), -1] i * (-Real.log (![(1 / 2 : ℝ), 1 / 2] i) - 1) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hR : ∑ i, ![(1 : ℝ), -1] i * -Real.log (![(2 / 3 : ℝ), 1 / 3] i) = -Real.log 2 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
      Real.log_one]
    ring
  rw [(hasDerivAt_entropy_diagPath hq _).deriv, (hasDerivAt_modEnergy_diagPath _ _ _).deriv, hL,
    hR]
  have := Real.log_pos one_lt_two
  intro h
  linarith

end

end ErEpr
