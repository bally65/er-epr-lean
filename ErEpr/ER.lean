import Mathlib

/-!
# ErEpr.ER：ER 側玩具零件（ER-1、ER-2）

mathlib 目前沒有 Levi-Civita 聯絡、Christoffel 符號、偽黎曼度規或 Riemann 曲率，
所以 ER 側全部在**顯式座標**裡做：度規以座標下的係數給出，定理談的是這些係數與曲線。

* **ER-1 橋不可穿越**（`no_causal_curve_between_exteriors`）：
  Kruskal 座標下的度規 `ds² = -F dU dV + A`（`F > 0`，`A ≥ 0` 是角向部分），
  指向未來的因果曲線上 U、V 都不減，所以沒有因果曲線連通左右兩個外區。
  * 見證：兩個外區各有一條因果曲線進入同一個未來內區（`meet_in_interior`）。
    兩邊的人可以在橋裡相遇，但誰也出不去。
  * 負控制：類空曲線確實連通兩個外區（`negctrl_spacelike_connects`），橋在空間上是連著的。
    所以「因果」這個條件不能拿掉。
* **ER-2 喉部是極小球面**（各向同性座標的 t = 0 切片，度規係數 `(1 + M/2ρ)⁴`）：
  * 球面面積 `≥ 16πM²`，在 `ρ = M/2` 達到（`throat_area_le`、`throat_area_eq`）；
  * 反演 `ρ ↦ M²/4ρ` 保持度規係數（`inversion_isometry`），交換兩個漸近端，喉部是它的不動點。

範圍（引用前請讀）：
* 只用到度規**係數的形式**。沒有證明它們滿足 Einstein 方程，也不是一般的拓撲審查定理
  （Friedman–Schleich–Witt 1993）。
* ER-2 是係數層級的恆等式，不是流形上的等距映射。
* 對應的 EPR 側在 `NoSignalling.lean`（不可通訊）與 `TFD.lean`（兩側互換）。
-/

namespace ErEpr

open Real

/-! ## ER-1：Kruskal 座標下的因果結構 -/

/-- 在 Kruskal 座標下，切向量 `(U', V')` 是「指向未來的因果向量」。
度規 `ds² = -F dU dV + A`，其中 `F > 0`、`A ≥ 0`（角向部分 `r² |Ω'|²`）；未來方向是 `U' + V' > 0`。 -/
def FutureCausal (F A U' V' : ℝ) : Prop :=
  0 < F ∧ 0 ≤ A ∧ -F * U' * V' + A ≤ 0 ∧ 0 < U' + V'

/-- 指向未來的因果向量，兩個 Kruskal 分量都非負。 -/
theorem FutureCausal.nonneg {F A U' V' : ℝ} (h : FutureCausal F A U' V') :
    0 ≤ U' ∧ 0 ≤ V' := by
  obtain ⟨hF, hA, hc, hf⟩ := h
  have hFp : 0 ≤ F * (U' * V') := by linarith
  have hp : 0 ≤ U' * V' := (mul_nonneg_iff_of_pos_left hF).mp hFp
  refine ⟨?_, ?_⟩
  · by_contra hU
    rw [not_le] at hU
    have hV : 0 < V' := by linarith
    have := mul_neg_of_neg_of_pos hU hV
    linarith
  · by_contra hV
    rw [not_le] at hV
    have hU : 0 < U' := by linarith
    have := mul_neg_of_pos_of_neg hU hV
    linarith

/-- 沿一條指向未來的因果曲線，Kruskal 座標 U、V 都不減。 -/
theorem kruskal_monotone {U V U' V' F A : ℝ → ℝ} {a b : ℝ}
    (hU : ∀ s ∈ Set.Icc a b, HasDerivAt U (U' s) s)
    (hV : ∀ s ∈ Set.Icc a b, HasDerivAt V (V' s) s)
    (hc : ∀ s ∈ Set.Icc a b, FutureCausal (F s) (A s) (U' s) (V' s)) :
    MonotoneOn U (Set.Icc a b) ∧ MonotoneOn V (Set.Icc a b) := by
  have key : ∀ W W' : ℝ → ℝ, (∀ s ∈ Set.Icc a b, HasDerivAt W (W' s) s) →
      (∀ s ∈ Set.Icc a b, 0 ≤ W' s) → MonotoneOn W (Set.Icc a b) := by
    intro W W' hW hW'
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact fun s hs => (hW s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hW s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hW s (interior_subset hs)).deriv]
      exact hW' s (interior_subset hs)
  exact ⟨key U U' hU fun s hs => (hc s hs).nonneg.1, key V V' hV fun s hs => (hc s hs).nonneg.2⟩

/-- 右外區：`U < 0 < V`。 -/
def RightExterior (U V : ℝ) : Prop := U < 0 ∧ 0 < V

/-- 左外區：`V < 0 < U`。 -/
def LeftExterior (U V : ℝ) : Prop := 0 < U ∧ V < 0

/-- 未來內區（黑洞內部）：`0 < U` 且 `0 < V`。 -/
def FutureInterior (U V : ℝ) : Prop := 0 < U ∧ 0 < V

/-- **ER-1 橋不可穿越**：沒有指向未來的因果曲線，從右外區走到左外區，反方向也不行。 -/
theorem no_causal_curve_between_exteriors {U V U' V' F A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : ∀ s ∈ Set.Icc a b, HasDerivAt U (U' s) s)
    (hV : ∀ s ∈ Set.Icc a b, HasDerivAt V (V' s) s)
    (hc : ∀ s ∈ Set.Icc a b, FutureCausal (F s) (A s) (U' s) (V' s)) :
    ¬ (RightExterior (U a) (V a) ∧ LeftExterior (U b) (V b)) ∧
      ¬ (LeftExterior (U a) (V a) ∧ RightExterior (U b) (V b)) := by
  obtain ⟨hUm, hVm⟩ := kruskal_monotone hU hV hc
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hVab := hVm ha hb hab
  have hUab := hUm ha hb hab
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    linarith
  · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    linarith

/-- 直線曲線 `s ↦ c + v s` 的導數。 -/
theorem hasDerivAt_affine (c v s : ℝ) : HasDerivAt (fun t => c + v * t) v s := by
  simpa using ((hasDerivAt_id s).const_mul v).const_add c

/-- **見證：在橋裡相遇**。右外區出發的 `(U, V) = (-1 + s, 1 + s)` 與左外區出發的
`(1 + s, -1 + s)` 都是指向未來的類光曲線，在 `s = 2` 都進入未來內區。
兩邊可以在黑洞內部相遇，但依 ER-1 不能把訊號送到對方的外區。 -/
theorem meet_in_interior :
    (∀ s : ℝ, HasDerivAt (fun t => -1 + 1 * t) 1 s) ∧
      (∀ s : ℝ, HasDerivAt (fun t => 1 + 1 * t) 1 s) ∧
      FutureCausal 1 0 1 1 ∧
      RightExterior (-1 + 1 * 0) (1 + 1 * 0) ∧ FutureInterior (-1 + 1 * 2) (1 + 1 * 2) ∧
      LeftExterior (1 + 1 * 0) (-1 + 1 * 0) ∧ FutureInterior (1 + 1 * 2) (-1 + 1 * 2) := by
  refine ⟨fun s => hasDerivAt_affine _ _ s, fun s => hasDerivAt_affine _ _ s, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp only [RightExterior, LeftExterior, FutureInterior, FutureCausal] <;> norm_num

/-- **見證：橋在空間上是連著的**。沿 t = 0 切片（`U = -V`）的 `(U, V) = (-1 + 2s, 1 - 2s)`，
切向量 `(2, -2)` 類空（`-F U' V' + A > 0`），從右外區（s = 0）走到左外區（s = 1）。 -/
theorem bridge_slice_spacelike :
    (∀ s : ℝ, HasDerivAt (fun t => -1 + 2 * t) 2 s) ∧
      (∀ s : ℝ, HasDerivAt (fun t => 1 + (-2) * t) (-2) s) ∧
      (∀ F : ℝ, 0 < F → 0 < -F * 2 * (-2) + 0) ∧
      RightExterior (-1 + 2 * 0) (1 + (-2) * 0) ∧ LeftExterior (-1 + 2 * 1) (1 + (-2) * 1) := by
  refine ⟨fun s => hasDerivAt_affine _ _ s, fun s => hasDerivAt_affine _ _ s, fun F hF => ?_,
    ?_, ?_⟩
  · nlinarith
  · simp only [RightExterior]; norm_num
  · simp only [LeftExterior]; norm_num

/-- **負控制：只拿掉「因果」、保留「指向未來」，結論就失敗**。
`(U, V) = (-1 + 3s, 1 - 2s)` 的切向量 `(3, -2)` 滿足 `U' + V' = 1 > 0`，但類空，
從右外區（s = 0）走到左外區（s = 1）。 -/
theorem negctrl_spacelike_connects :
    (∀ s : ℝ, HasDerivAt (fun t => -1 + 3 * t) 3 s) ∧
      (∀ s : ℝ, HasDerivAt (fun t => 1 + (-2) * t) (-2) s) ∧
      (0 : ℝ) < 3 + (-2) ∧ (∀ F A : ℝ, 0 < F → 0 ≤ A → 0 < -F * 3 * (-2) + A) ∧
      RightExterior (-1 + 3 * 0) (1 + (-2) * 0) ∧ LeftExterior (-1 + 3 * 1) (1 + (-2) * 1) := by
  refine ⟨fun s => hasDerivAt_affine _ _ s, fun s => hasDerivAt_affine _ _ s, by norm_num,
    fun F A hF hA => ?_, ?_, ?_⟩
  · nlinarith
  · simp only [RightExterior]; norm_num
  · simp only [LeftExterior]; norm_num

/-! ## ER-2：Einstein–Rosen 橋的喉部 -/

/-- 各向同性座標下 t = 0 切片的共形因子 `(1 + M/2ρ)⁴`：度規 `g = (1 + M/2ρ)⁴ (dρ² + ρ² dΩ²)`。 -/
noncomputable def confIso (M ρ : ℝ) : ℝ := (1 + M / (2 * ρ)) ^ 4

/-- 半徑座標 ρ 處的球面面積 `4π ρ² (1 + M/2ρ)⁴`。 -/
noncomputable def areaIso (M ρ : ℝ) : ℝ := 4 * π * ρ ^ 2 * confIso M ρ

theorem areaIso_eq {M ρ : ℝ} (hρ : 0 < ρ) : areaIso M ρ = 4 * π * (ρ + M / 2) ^ 4 / ρ ^ 2 := by
  rw [areaIso, confIso]
  field_simp

/-- **ER-2 喉部是極小球面**：所有球面的面積都 `≥ 16πM²`。 -/
theorem throat_area_le {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) : 16 * π * M ^ 2 ≤ areaIso M ρ := by
  rw [areaIso_eq hρ, le_div_iff₀ (by positivity)]
  have h1 : 2 * M * ρ ≤ (ρ + M / 2) ^ 2 := by nlinarith [sq_nonneg (ρ - M / 2)]
  have h2 : (2 * M * ρ) ^ 2 ≤ ((ρ + M / 2) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  nlinarith [Real.pi_pos]

/-- 最小值 `16πM² = 4π(2M)²` 在 `ρ = M/2` 達到，也就是 Schwarzschild 半徑 `2M` 的球面面積。 -/
theorem throat_area_eq {M : ℝ} (hM : 0 < M) : areaIso M (M / 2) = 16 * π * M ^ 2 := by
  rw [areaIso, confIso]
  field_simp
  ring

/-- 反演 `ρ ↦ M²/4ρ` 的導數。 -/
theorem hasDerivAt_inversion {M ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun x => M ^ 2 / (4 * x)) (-(M ^ 2 / (4 * ρ ^ 2))) ρ := by
  have e : (fun x : ℝ => M ^ 2 / (4 * x)) = fun x => M ^ 2 / 4 * x⁻¹ := by
    funext x
    ring
  rw [e]
  exact ((hasDerivAt_inv hρ.ne').const_mul (M ^ 2 / 4)).congr_deriv (by ring)

/-- **ER-2 反演對稱**：`ι(ρ) = M²/4ρ` 保持度規係數。
* 徑向：`confIso(ι ρ) · ι'(ρ)² = confIso(ρ)`；
* 角向：`confIso(ι ρ) · ι(ρ)² = confIso(ρ) · ρ²`。
它交換 `ρ → ∞` 與 `ρ → 0` 兩個漸近端。 -/
theorem inversion_isometry {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    confIso M (M ^ 2 / (4 * ρ)) * (-(M ^ 2 / (4 * ρ ^ 2))) ^ 2 = confIso M ρ ∧
      confIso M (M ^ 2 / (4 * ρ)) * (M ^ 2 / (4 * ρ)) ^ 2 = confIso M ρ * ρ ^ 2 := by
  constructor <;> (rw [confIso, confIso]; field_simp; ring)

/-- 喉部 `ρ = M/2` 是反演的不動點。 -/
theorem inversion_fixed {M : ℝ} (hM : 0 < M) : M ^ 2 / (4 * (M / 2)) = M / 2 := by
  field_simp
  ring

end ErEpr
