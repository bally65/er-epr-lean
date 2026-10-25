import ErEpr.Basic

/-!
# ErEpr.GammaRotation：複數速率的 Gamma 積分

mathlib 有實數速率版 `integral_cpow_mul_exp_neg_mul_Ioi`：`r > 0` 時
`∫_0^∞ t^{a−1} e^{−rt} dt = (1/r)^a Γ(a)`。Bogoliubov 係數需要**複數**速率 `r = δ ± ik`
（振盪積分加上正則化），mathlib 沒有。本檔用解析函數的唯一性定理補上：

* `F(r) = ∫_0^∞ t^{a−1} e^{−rt} dt` 在右半平面 `Re r > 0` 上複可微（`differentiableAt_gammaIntegral`，
  參數積分在積分號下微分，界 `t^{Re a} e^{−(Re r₀/2)t}`）；
* `G(r) = (1/r)^a Γ(a)` 在右半平面上複可微；
* 兩者在正實軸上相等（mathlib 的實數版），右半平面連通，所以處處相等
  （`integral_gammaKernel`）。

這是純分析的引理，沒有任何物理內容；物理讀法見 `ErEpr/Unruh.lean`。
-/

namespace ErEpr

open Complex MeasureTheory Set Filter Topology Metric

noncomputable section

/-- 被積函數 `t^{a−1}·e^{−rt}`。 -/
def gammaKernel (a r : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (a - 1) * Complex.exp (-(r * t))

theorem norm_gammaKernel {a r : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖gammaKernel a r t‖ = t ^ (a.re - 1) * Real.exp (-(r.re * t)) := by
  rw [gammaKernel, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp [Complex.mul_re]

theorem continuousOn_gammaKernel (a r : ℂ) : ContinuousOn (gammaKernel a r) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold gammaKernel
  exact (continuousAt_ofReal_cpow_const t (a - 1) (Or.inr (ne_of_gt ht))).mul
    (Complex.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ => -(r * (t : ℂ)))).continuousAt

theorem integrableOn_gammaKernel {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    IntegrableOn (gammaKernel a r) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a.re - 1) (p := 1) (b := r.re)
    (by linarith) one_pos hr
  refine Integrable.mono' hb ((continuousOn_gammaKernel a r).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  exact le_of_eq (by rw [norm_gammaKernel ht, Real.rpow_one, neg_mul])

theorem hasDerivAt_gammaKernel (a : ℂ) (t : ℝ) (r : ℂ) :
    HasDerivAt (fun r => gammaKernel a r t) (-(t : ℂ) * gammaKernel a r t) r := by
  unfold gammaKernel
  have h0 : HasDerivAt (fun x : ℂ => -(x * (t : ℂ))) (-(t : ℂ)) r :=
    (hasDerivAt_mul_const (t : ℂ) (x := r)).neg
  refine (h0.cexp.const_mul ((t : ℂ) ^ (a - 1))).congr_deriv ?_
  ring

/-- `F(r) = ∫_0^∞ t^{a−1} e^{−rt} dt` 在右半平面複可微。 -/
theorem differentiableAt_gammaIntegral {a r₀ : ℂ} (ha : 0 < a.re) (hr₀ : 0 < r₀.re) :
    DifferentiableAt ℂ (fun r => ∫ t in Ioi (0 : ℝ), gammaKernel a r t) r₀ := by
  set c := r₀.re / 2 with hc
  have hc0 : 0 < c := half_pos hr₀
  have hs : ball r₀ c ∈ 𝓝 r₀ := ball_mem_nhds r₀ hc0
  have hre : ∀ r ∈ ball r₀ c, c < r.re := by
    intro r hr
    rw [mem_ball, dist_eq_norm] at hr
    have h1 : |(r - r₀).re| ≤ ‖r - r₀‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hr)
    linarith [h2.1]
  have hbound := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a.re) (p := 1) (b := c)
    (by linarith) one_pos hc0
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))), ∀ r ∈ ball r₀ c,
      ‖-(t : ℂ) * gammaKernel a r t‖ ≤ t ^ a.re * Real.exp (-c * t ^ (1 : ℝ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht r hr => ?_
    have ht' : 0 < t := ht
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht',
      norm_gammaKernel ht', Real.rpow_one]
    have hpow : t * t ^ (a.re - 1) = t ^ a.re := by
      rw [Real.rpow_sub_one ht'.ne', mul_div_cancel₀ _ ht'.ne']
    have hexp : Real.exp (-(r.re * t)) ≤ Real.exp (-c * t) := by
      apply Real.exp_le_exp.mpr
      have := hre r hr
      nlinarith
    calc t * (t ^ (a.re - 1) * Real.exp (-(r.re * t)))
        = t ^ a.re * Real.exp (-(r.re * t)) := by rw [← mul_assoc, hpow]
      _ ≤ t ^ a.re * Real.exp (-c * t) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht'.le _)
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -(t : ℂ) * gammaKernel a r₀ t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((Complex.continuous_ofReal.neg.continuousOn).mul
      (continuousOn_gammaKernel a r₀)).aestronglyMeasurable measurableSet_Ioi
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r t => gammaKernel a r t) (F' := fun r t => -(t : ℂ) * gammaKernel a r t)
    (bound := fun t => t ^ a.re * Real.exp (-c * t ^ (1 : ℝ))) hs
    (Eventually.of_forall fun r =>
      (continuousOn_gammaKernel a r).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_gammaKernel ha hr₀) hmeas' hb hbound
    (ae_of_all _ fun t r _ => hasDerivAt_gammaKernel a t r)).2
  exact hd.differentiableAt

/-- **複數速率的 Gamma 積分**：`Re a > 0`、`Re r > 0` ⇒ `∫_0^∞ t^{a−1} e^{−rt} dt = (1/r)^a Γ(a)`。 -/
theorem integral_gammaKernel {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), gammaKernel a r t = (1 / r) ^ a * Complex.Gamma a := by
  have hUo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ (fun z => ∫ t in Ioi (0 : ℝ), gammaKernel a z t) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_gammaIntegral ha hz).differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => (1 / z) ^ a * Complex.Gamma a) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz' : 0 < z.re := hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz'; exact lt_irrefl 0 hz'
    have hslit : 1 / z ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      rw [one_div, Complex.inv_re]
      exact div_pos hz' (Complex.normSq_pos.mpr hz0)
    have hinv : DifferentiableAt ℂ (fun z : ℂ => 1 / z) z := by
      simp only [one_div]
      exact differentiableAt_inv hz0
    exact ((hinv.cpow_const hslit).mul_const _).differentiableWithinAt
  have hU : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt (r := 0)).isPreconnected
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < (1 : ℂ).re
    rw [Complex.one_re]
    exact one_pos
  have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h0
      have := (Complex.continuous_ofReal.tendsto 1).comp h0
      rw [Complex.ofReal_one] at this
      exact this
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h' := Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      (fun z => ∫ t in Ioi (0 : ℝ), gammaKernel a z t) z = (fun z : ℂ => (1 / z) ^ a * Complex.Gamma a) z :=
    hseq.frequently (Frequently.of_forall fun n =>
      integral_cpow_mul_exp_neg_mul_Ioi ha (by positivity))
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hU h1 hfreq hr

end

end ErEpr
