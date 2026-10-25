import ErEpr.Charts
import ErEpr.GammaRotation

/-!
# ErEpr.Unruh：類比重力的核心定理（CHAIN_DESIGN §10 的 X₁′）

Unruh／Hawking 效應的**運動學核心**：一維波動方程式加一個視界（表面重力 κ），視界兩側模態的
Bogoliubov 係數滿足 `|β_ω|² = e^{−2πω/κ}|α_ω|²`，出射態是溫度 `κ/2π` 的熱態。
它不需要 Einstein 方程，也不需要真的重力，所以超冷原子聲學視界（Steinhauer 2016、2019）
與水槽（Weinfurtner 2011）實驗量到的就是這一層。

本檔分三塊（每塊的陳述只談實數、複數與積分；物理名詞只在說明文字裡）：

1. **熱分佈**（`bogoliubov_thermal`）：若 `|β|² = e^{−2πω/κ}|α|²` 且 `|α|² − |β|² = 1`
   （玻色子的正則對易關係），則 `|β|²` 等於逆溫度 `2π/κ` 的諧振子平均佔據數。
   平均佔據數**獨立定義**成 Boltzmann 加權平均 `Σ n e^{−βωn} / Σ e^{−βωn}`（`meanOccupation`），
   並證它等於 Bose–Einstein 的 `1/(e^{βω} − 1)`（`meanOccupation_eq`）。所以「熱」不是用係數比定義的。
   負控制 `negctrl_bogoliubov_fermi`：對易關係寫成費米子的 `|α|² + |β|² = 1`，得到 Fermi–Dirac，不是熱的玻色佔據數。
2. **表面重力與溫度**（`hasDerivAt_FS_horizon`、`unitConeAngle_of_surfaceGravity`）：
   Schwarzschild 的 `F(r) = 1 − 2M/r` 在視界 `r = 2M` 的斜率給 `κ = F′(2M)/2 = 1/(4M)`，
   `β = 2π/κ = 8πM`，正好滿足 ER-3 的單位錐角條件（`hawking_beta`）。
   兩條獨立的路（錐角、表面重力）得到同一個溫度；耦合斷言確認表面重力那條路不經 `hawking_beta`。
3. **Bogoliubov 係數比**（見檔尾）：Rindler 模態與 Minkowski 模態的重疊積分
   `∫_0^∞ x^{a−1} e^{∓ikx} dx`（`a = ε + iΩ`、`Ω = ω/κ`，正則化 `e^{−δx}`）由
   `ErEpr/GammaRotation.lean` 的複數速率 Gamma 積分算出；兩者的模長比在 `δ → 0` 時趨向 `e^{−πΩ}`，
   平方後就是 `e^{−2πω/κ}`。

範圍（引用前請讀）：
* 「這兩個積分就是 Bogoliubov 係數（差一個共同的歸一化）」是物理的設定，寫在說明文字裡，不是定理。
* 正則對易關係 `|α|² − |β|² = 1` 在第 1 塊是**假設**，不是從模態內積推出來的。
* 只做 1+1 維、單一模態；沒有灰體因子、沒有反作用。
-/

namespace ErEpr

open Real

noncomputable section

/-! ## 1. 熱分佈 -/

/-- 諧振子模態（頻率 `ω`）在逆溫度 `β` 的平均佔據數，直接由 Boltzmann 權重定義。 -/
def meanOccupation (β ω : ℝ) : ℝ :=
  (∑' n : ℕ, (n : ℝ) * Real.exp (-(β * ω)) ^ n) / ∑' n : ℕ, Real.exp (-(β * ω)) ^ n

/-- **Bose–Einstein**：`βω > 0` ⇒ `n̄ = 1/(e^{βω} − 1)`。 -/
theorem meanOccupation_eq {β ω : ℝ} (h : 0 < β * ω) :
    meanOccupation β ω = 1 / (Real.exp (β * ω) - 1) := by
  rw [meanOccupation]
  set x := Real.exp (-(β * ω)) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    rw [hx, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hS : ∑' n : ℕ, x ^ n = (1 - x)⁻¹ := tsum_geometric_of_lt_one hx0.le hx1
  have hN : ∑' n : ℕ, (n : ℝ) * x ^ n = x / (1 - x) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_pos hx0]; exact hx1)
  have he : Real.exp (β * ω) = x⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
  have h1x : 1 - x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hx0' : x ≠ 0 := hx0.ne'
  have hd : x⁻¹ - 1 ≠ 0 := by
    have := (one_lt_inv₀ hx0).mpr hx1
    linarith
  rw [hS, hN, he]
  field_simp

/-- **係數比＋正則對易關係 ⇒ 熱分佈**。`A = |α|²`、`B = |β|²`。 -/
theorem bogoliubov_thermal {A B ω κ : ℝ} (hκ : 0 < κ) (hω : 0 < ω)
    (hratio : B = Real.exp (-(2 * π / κ * ω)) * A) (hccr : A - B = 1) :
    B = meanOccupation (2 * π / κ) ω := by
  have hpos : 0 < 2 * π / κ * ω := mul_pos (div_pos (mul_pos two_pos pi_pos) hκ) hω
  rw [meanOccupation_eq hpos]
  set x := Real.exp (-(2 * π / κ * ω)) with hx
  have hx0 : x ≠ 0 := (Real.exp_pos _).ne'
  have hx1 : x < 1 := by
    rw [hx, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have he : Real.exp (2 * π / κ * ω) = x⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hden : x⁻¹ - 1 ≠ 0 := by
    have := (one_lt_inv₀ (Real.exp_pos _)).mpr hx1
    linarith
  rw [he, eq_div_iff hden]
  linear_combination x⁻¹ * hratio + hccr + A * hinv

/-- **負控制**：對易關係寫成費米子的 `|α|² + |β|² = 1`，同一個係數比給出 Fermi–Dirac 的
`1/(e^{βω} + 1)`，不是熱的玻色佔據數。 -/
theorem negctrl_bogoliubov_fermi {A B ω κ : ℝ} (hκ : 0 < κ) (hω : 0 < ω)
    (hratio : B = Real.exp (-(2 * π / κ * ω)) * A) (hcar : A + B = 1) :
    B = 1 / (Real.exp (2 * π / κ * ω) + 1) ∧ B ≠ meanOccupation (2 * π / κ) ω := by
  have hpos : 0 < 2 * π / κ * ω := mul_pos (div_pos (mul_pos two_pos pi_pos) hκ) hω
  set x := Real.exp (-(2 * π / κ * ω)) with hx
  have hx0 : x ≠ 0 := (Real.exp_pos _).ne'
  have he : Real.exp (2 * π / κ * ω) = x⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hden : x⁻¹ + 1 ≠ 0 := by
    have := inv_pos.mpr (Real.exp_pos (-(2 * π / κ * ω)))
    linarith
  have hB : B = 1 / (Real.exp (2 * π / κ * ω) + 1) := by
    rw [he, eq_div_iff hden]
    linear_combination x⁻¹ * hratio + hcar + A * hinv
  refine ⟨hB, fun h => ?_⟩
  rw [meanOccupation_eq hpos, hB, one_div, one_div, inv_inj] at h
  linarith

/-! ## 2. 表面重力與溫度 -/

/-- Schwarzschild 的表面重力：`F(r) = 1 − 2M/r` 在視界 `r = 2M` 的斜率是 `2κ`，`κ = 1/(4M)`。 -/
theorem hasDerivAt_FS_horizon {M : ℝ} (hM : 0 < M) :
    HasDerivAt (FS M) (2 * (1 / (4 * M))) (2 * M) := by
  have h2M : (2 * M : ℝ) ≠ 0 := (mul_pos two_pos hM).ne'
  have hinv := ((hasDerivAt_inv h2M).const_mul (2 * M)).const_sub 1
  have hfun : FS M = fun y => 1 - 2 * M * y⁻¹ := by
    funext y
    rw [FS, div_eq_mul_inv]
  rw [hfun]
  refine hinv.congr_deriv ?_
  have hM0 : M ≠ 0 := hM.ne'
  field_simp
  norm_num

/-- `κ = F′(2M)/2 = 1/(4M)`。 -/
theorem surfaceGravity_schwarzschild {M : ℝ} (hM : 0 < M) :
    deriv (FS M) (2 * M) / 2 = 1 / (4 * M) := by
  rw [(hasDerivAt_FS_horizon hM).deriv]
  ring

/-- **兩條獨立的路，同一個溫度**：表面重力給的 `β = 2π/κ` 滿足 ER-3 的單位錐角條件。 -/
theorem unitConeAngle_of_surfaceGravity {M : ℝ} (hM : 0 < M) :
    UnitConeAngle M (2 * π / (deriv (FS M) (2 * M) / 2)) := by
  rw [surfaceGravity_schwarzschild hM, hawking_beta hM, div_div_eq_mul_div, div_one]
  ring

/-! ## 3. Bogoliubov 係數比 -/

open Complex MeasureTheory Set Filter Topology in
/-- **正則化的係數比**：`a = ε + iΩ`（`ε > 0`）、`δ > 0`。重疊積分
`∫_0^∞ x^{a−1} e^{−(δ ∓ ik)x} dx` 的模長比恰好是 `exp(−2Ω·arg(δ + ik))`，與 `ε` 無關；
`k` 可以是任何實數（`k > 0` 只在取視界極限 `bogoliubov_ratio_tendsto` 時才需要）。 -/
theorem bogoliubov_ratio_regularized {ε Ω δ k : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + Ω * I) (δ - k * I) t‖ /
        ‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + Ω * I) (δ + k * I) t‖ =
      Real.exp (-2 * Ω * Complex.arg (δ + k * I)) := by
  have ha : 0 < ((ε : ℂ) + Ω * I).re := by simp [hε]
  have him : ((ε : ℂ) + Ω * I).im = Ω := by simp
  have hrp : 0 < ((δ : ℂ) + k * I).re := by simp [hδ]
  have hrm : 0 < ((δ : ℂ) - k * I).re := by simp [hδ]
  have hconj : (δ : ℂ) - k * I = (starRingEnd ℂ) ((δ : ℂ) + k * I) := by
    apply Complex.ext <;> simp
  have hrp0 : (δ : ℂ) + k * I ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hrp
    exact lt_irrefl 0 hrp
  have hrm0 : (δ : ℂ) - k * I ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hrm
    exact lt_irrefl 0 hrm
  have hargp : Complex.arg ((δ : ℂ) + k * I) ≠ π := by
    have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrp)
    intro h
    rw [h, abs_of_pos Real.pi_pos] at h1
    linarith [Real.pi_pos]
  have hargm : Complex.arg ((δ : ℂ) - k * I) = -Complex.arg ((δ : ℂ) + k * I) := by
    rw [hconj, Complex.arg_conj, if_neg hargp]
  have hargm' : Complex.arg ((δ : ℂ) - k * I) ≠ π := by
    rw [hargm]
    intro h
    have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrp)
    rw [show Complex.arg ((δ : ℂ) + k * I) = -π by linarith, abs_neg, abs_of_pos Real.pi_pos] at h1
    linarith [Real.pi_pos]
  have hinvp : Complex.arg (1 / ((δ : ℂ) + k * I)) = -Complex.arg ((δ : ℂ) + k * I) := by
    rw [one_div, Complex.arg_inv, if_neg hargp]
  have hinvm : Complex.arg (1 / ((δ : ℂ) - k * I)) = Complex.arg ((δ : ℂ) + k * I) := by
    rw [one_div, Complex.arg_inv, if_neg hargm', hargm, neg_neg]
  have hnorm : ‖1 / ((δ : ℂ) - k * I)‖ = ‖1 / ((δ : ℂ) + k * I)‖ := by
    rw [norm_div, norm_div, hconj, Complex.norm_conj]
  rw [integral_gammaKernel ha hrm, integral_gammaKernel ha hrp, norm_mul, norm_mul,
    Complex.norm_cpow_of_ne_zero (one_div_ne_zero hrm0),
    Complex.norm_cpow_of_ne_zero (one_div_ne_zero hrp0), hinvm, hinvp, hnorm, him]
  have hG : ‖Complex.Gamma ((ε : ℂ) + Ω * I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ha)
  have hN : ‖1 / ((δ : ℂ) + k * I)‖ ^ ((ε : ℂ) + Ω * I).re ≠ 0 :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr (one_div_ne_zero hrp0)) _).ne'
  have h1 : Real.exp (Complex.arg ((δ : ℂ) + k * I) * Ω) ≠ 0 := Real.exp_ne_zero _
  have h2 : Real.exp (-Complex.arg ((δ : ℂ) + k * I) * Ω) ≠ 0 := Real.exp_ne_zero _
  have key : ∀ N G e₁ e₂ : ℝ, N ≠ 0 → G ≠ 0 → e₁ ≠ 0 → e₂ ≠ 0 →
      N / e₁ * G / (N / e₂ * G) = e₂ / e₁ := by
    intro N G e₁ e₂ hN hG h₁ h₂
    field_simp
  rw [key _ _ _ _ hN hG h1 h2, ← Real.exp_sub]
  congr 1
  ring

open Complex MeasureTheory Set Filter Topology in
/-- **視界極限**：`δ → 0⁺` 時係數比趨向 `e^{−πΩ}`。 -/
theorem bogoliubov_ratio_tendsto {ε Ω k : ℝ} (hε : 0 < ε) (hk : 0 < k) :
    Tendsto (fun δ : ℝ => ‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + Ω * I) (δ - k * I) t‖ /
        ‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + Ω * I) (δ + k * I) t‖) (𝓝[>] 0)
      (𝓝 (Real.exp (-(π * Ω)))) := by
  have hslit : ((0 : ℝ) : ℂ) + k * I ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simp [hk.ne']))
  have harg : Complex.arg (((0 : ℝ) : ℂ) + k * I) = π / 2 := by
    rw [Complex.ofReal_zero, zero_add, Complex.arg_real_mul _ hk, Complex.arg_I]
  have h1 : ContinuousAt (fun δ : ℝ => Complex.arg ((δ : ℂ) + k * I)) 0 :=
    (Complex.continuousAt_arg hslit).comp (f := fun δ : ℝ => (δ : ℂ) + k * I) (by fun_prop)
  have h2 : Tendsto (fun δ : ℝ => Real.exp (-2 * Ω * Complex.arg ((δ : ℂ) + k * I))) (𝓝 0)
      (𝓝 (Real.exp (-2 * Ω * Complex.arg (((0 : ℝ) : ℂ) + k * I)))) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto _).comp h1.tendsto
  rw [harg, show -2 * Ω * (π / 2) = -(π * Ω) by ring] at h2
  exact (h2.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun δ hδ => (bogoliubov_ratio_regularized (k := k) hε hδ).symm)

open Complex MeasureTheory Set Filter Topology in
/-- **X₁′（Unruh 核心）**：`Ω = ω/κ` 時，係數比的平方在視界極限下趨向 `e^{−2πω/κ}`，
也就是 `bogoliubov_thermal` 需要的那個比值（逆溫度 `2π/κ`）。 -/
theorem bogoliubov_ratio_sq_tendsto {ε ω κ k : ℝ} (hε : 0 < ε) (hk : 0 < k) :
    Tendsto (fun δ : ℝ =>
        (‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + ((ω / κ : ℝ) : ℂ) * I) (δ - k * I) t‖ /
          ‖∫ t in Ioi (0 : ℝ), gammaKernel (ε + ((ω / κ : ℝ) : ℂ) * I) (δ + k * I) t‖) ^ 2)
      (𝓝[>] 0) (𝓝 (Real.exp (-(2 * π / κ * ω)))) := by
  have h := (bogoliubov_ratio_tendsto (Ω := ω / κ) hε hk).pow 2
  have he : Real.exp (-(π * (ω / κ))) ^ 2 = Real.exp (-(2 * π / κ * ω)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he] at h
  exact h

/-- **Schwarzschild**：`κ = F′(2M)/2` 代入，熱因子是 `e^{−8πMω}`，逆溫度 `8πM`（與 `hawking_beta` 同一個 β）。 -/
theorem bogoliubov_factor_schwarzschild {M ω : ℝ} (hM : 0 < M) :
    Real.exp (-(2 * π / (deriv (FS M) (2 * M) / 2) * ω)) = Real.exp (-(8 * π * M * ω)) := by
  rw [surfaceGravity_schwarzschild hM, div_div_eq_mul_div, div_one]
  congr 1
  ring

open Filter Topology in
/-- **負控制：沒有視界就沒有熱輻射**。`κ → 0⁺` 時熱因子 `e^{−2πω/κ} → 0`：`|β|² → 0`。 -/
theorem negctrl_no_horizon {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun κ : ℝ => Real.exp (-(2 * π / κ * ω))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun κ : ℝ => (2 * π * ω) * κ⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  refine h2.congr' (Eventually.of_forall fun κ => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

end

end ErEpr
