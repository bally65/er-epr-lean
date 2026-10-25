import ErEpr.ER

/-!
# ErEpr.Hawking：ER-3 單位錐角條件與 Hawking 溫度，與收尾 S = A/4

* **ER-3**（`hawking_beta`）：Schwarzschild 解的歐氏度規 `F(r) dτ² + dr²/F(r)`（`F = 1 - 2M/r`），
  τ 的週期是 β。在視界處取比值
  「τ 圓周長 `β√F` ÷（2π × 到視界的固有距離）」的極限（一般形式是 `coneAngleRatio`）。
  * 這個極限等於 `β / 8πM`（`conicalRatio_tendsto`）；
  * 所以**單位錐角條件**（極限為 1，`UnitConeAngle`）⇔ `β = 8πM`。
  * 單位錐角條件是視界處沒有錐狀奇點的**一階必要條件**，不是充分條件。
    充分性（笛卡兒圖下度規分量光滑）本庫未證，見 `docs/CHAIN_DESIGN.md` §1 X₁。
  * 反過來，比值極限不是 1 時必要條件失敗，確實有錐狀奇點：
    `β = 4πM` 時極限是 1/2（`negctrl_wrong_beta`）。
  * 真錐見證：錐角 `2πc` 的平面錐，這個比值恰為 `c`（`coneAngleRatio_cone`）；
    `c ≠ 1` 時不滿足單位錐角條件（`coneAngleRatio_cone_not_unit`）。
* 固有距離用變數 `r = 2M + x²` 寫成 `ρ(x) = ∫₀ˣ 2√(2M + t²) dt`。
  它在 r 變數下的導數是 `1/√F(r)`（`properDist_r_hasDerivAt`），所以確實是固有距離。
* **收尾**（`first_law_area`）：若熵滿足 `S(0) = 0`、`dS/dm = β(m)`，
  而且每個 `m > 0` 的 `β(m)` 都滿足單位錐角條件，則 `S(M) = 4πM² = A/4`，A 是 ER-2 的喉部面積。
  * `S(0) = 0` 釘死了積分常數：拿掉它，`4πm² + c`（`c ≠ 0`）滿足其餘全部假設，
    結論卻不成立（`negctrl_first_law_const`）。

範圍（引用前請讀）：
* 單位錐角條件只是一個比值的極限，不是光滑流形的建構；它只是光滑的一階必要條件。
  「β = 8πM ⇒ 視界光滑」本庫沒有證明。
* 收尾假設了能量就是質量 `E = M`、第一定律 `dS = dE/T`、`T = 1/β`；沒有任何量子重力輸入。
  它是 Bekenstein–Hawking 關係在座標層級的一致性檢查，不是推導。
* 「黑洞的微觀 Gibbs 熵 = 這個熱力學熵」沒有形式化，也無法形式化：那需要量子重力。
-/

namespace ErEpr

open Real Filter Topology

/-! ## 固有距離 -/

/-- 視界外的固有徑向距離，用變數 `r = 2M + x²` 寫：`ρ(x) = ∫₀ˣ 2√(2M + t²) dt`。 -/
noncomputable def properDist (M x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, 2 * √(2 * M + t ^ 2)

theorem continuous_properDist_integrand (M : ℝ) :
    Continuous fun t : ℝ => 2 * √(2 * M + t ^ 2) :=
  continuous_const.mul ((continuous_const.add (continuous_pow 2)).sqrt)

theorem properDist_hasDerivAt (M x : ℝ) :
    HasDerivAt (properDist M) (2 * √(2 * M + x ^ 2)) x :=
  ((continuous_properDist_integrand M).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem properDist_zero (M : ℝ) : properDist M 0 = 0 := intervalIntegral.integral_same

/-- **保真**：在 r 變數下 `dρ/dr = 1/√F(r)`，`F(r) = 1 - 2M/r`，所以 `properDist` 確實是固有距離。 -/
theorem properDist_r_hasDerivAt {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    HasDerivAt (fun r => properDist M (√(r - 2 * M))) (1 / √(1 - 2 * M / r)) r := by
  have hpos : 0 < r - 2 * M := by linarith
  have hr0 : 0 < r := by linarith
  have h1 : HasDerivAt (fun r => √(r - 2 * M)) (1 / (2 * √(r - 2 * M))) r :=
    ((hasDerivAt_id r).sub_const (2 * M)).sqrt hpos.ne'
  have h2 := (properDist_hasDerivAt M (√(r - 2 * M))).comp r h1
  refine h2.congr_deriv ?_
  have hs1 : √(r - 2 * M) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs2 : √r ≠ 0 := (Real.sqrt_pos.mpr hr0).ne'
  rw [sq_sqrt hpos.le, show 2 * M + (r - 2 * M) = r by ring,
    show 1 - 2 * M / r = (r - 2 * M) / r by field_simp, sqrt_div hpos.le]
  field_simp

/-! ## ER-3：錐狀奇點的比值與 Hawking 溫度 -/

/-- 一般的錐角比值：「圓周長 `circ x` ÷（2π × 固有距離 `dist x`）」。
度規在原點光滑的一階必要條件是它在原點的極限為 1；錐角 `2πc` 的錐，這個比值恰為 `c`。 -/
noncomputable def coneAngleRatio (circ dist : ℝ → ℝ) (x : ℝ) : ℝ := circ x / (2 * π * dist x)

/-- 歐氏時間週期為 β 時，`r = 2M + x²` 處的比值
「τ 圓周長 `β √F(r)` ÷（2π × 到視界的固有距離）」。 -/
noncomputable def conicalRatio (M β x : ℝ) : ℝ :=
  β * √(1 - 2 * M / (2 * M + x ^ 2)) / (2 * π * properDist M x)

/-- `conicalRatio` 就是 `coneAngleRatio` 取 Schwarzschild 的圓周長與固有距離。 -/
theorem conicalRatio_eq_coneAngleRatio (M β x : ℝ) :
    conicalRatio M β x =
      coneAngleRatio (fun x => β * √(1 - 2 * M / (2 * M + x ^ 2))) (properDist M) x := rfl

/-- **真錐見證**：`c > 0` 時這是錐角 `2πc` 的平面錐（距原點 `x` 處的圓周長是 `2πc·x`、
固有距離是 `x`）。比值恆等於 `c`，所以極限是 `c`；`c ≠ 1` 時就有錐狀奇點。
（陳述對所有實數 `c` 都成立，`c > 0` 只是讓它有錐的幾何意義。） -/
theorem coneAngleRatio_cone (c : ℝ) :
    Tendsto (coneAngleRatio (fun x => 2 * π * c * x) (fun x => x)) (𝓝[>] 0) (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  show c = 2 * π * c * x / (2 * π * x)
  rw [eq_div_iff (mul_pos (mul_pos two_pos pi_pos) hx).ne']
  ring

/-- `c ≠ 1` 的錐不滿足單位錐角條件。 -/
theorem coneAngleRatio_cone_not_unit {c : ℝ} (hc1 : c ≠ 1) :
    ¬ Tendsto (coneAngleRatio (fun x => 2 * π * c * x) (fun x => x)) (𝓝[>] 0) (𝓝 1) :=
  fun h => hc1 (tendsto_nhds_unique (coneAngleRatio_cone c) h)

/-- **單位錐角條件**：視界處比值的極限為 1。這是沒有錐狀奇點的一階必要條件，不是充分條件；
充分性（笛卡兒圖下度規分量光滑）本庫未證，見 `docs/CHAIN_DESIGN.md` §1 X₁。 -/
abbrev UnitConeAngle (M β : ℝ) : Prop := Tendsto (conicalRatio M β) (𝓝[>] 0) (𝓝 1)

theorem sqrtF_sub {M x : ℝ} (hM : 0 < M) (hx : 0 < x) :
    √(1 - 2 * M / (2 * M + x ^ 2)) = x / √(2 * M + x ^ 2) := by
  have h : 0 < 2 * M + x ^ 2 := by positivity
  rw [show 1 - 2 * M / (2 * M + x ^ 2) = x ^ 2 / (2 * M + x ^ 2) by field_simp; ring,
    sqrt_div (sq_nonneg x), sqrt_sq hx.le]

/-- 視界處比值的極限是 `β / 8πM`。 -/
theorem conicalRatio_tendsto {M : ℝ} (hM : 0 < M) (β : ℝ) :
    Tendsto (conicalRatio M β) (𝓝[>] 0) (𝓝 (β / (8 * π * M))) := by
  have hs0 : 0 < √(2 * M) := Real.sqrt_pos.mpr (by linarith)
  -- 固有距離 / x → 2√(2M)（導數在 0 的斜率極限）
  have hslope : Tendsto (fun x => properDist M x / x) (𝓝[>] 0) (𝓝 (2 * √(2 * M))) := by
    have hd := properDist_hasDerivAt M 0
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at hd
    have h' : Tendsto (slope (properDist M) 0) (𝓝[>] 0) (𝓝 (2 * √(2 * M))) :=
      (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')
    refine h'.congr fun x => ?_
    rw [slope_def_field, properDist_zero, sub_zero, sub_zero]
  -- 1/√(2M + x²) → 1/√(2M)
  have h0 : Tendsto (fun x : ℝ => 2 * M + x ^ 2) (𝓝[>] 0) (𝓝 (2 * M)) := by
    have hcont : Continuous fun x : ℝ => 2 * M + x ^ 2 := continuous_const.add (continuous_pow 2)
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have hc : Tendsto (fun x => 1 / √(2 * M + x ^ 2)) (𝓝[>] 0) (𝓝 (1 / √(2 * M))) :=
    tendsto_const_nhds.div h0.sqrt hs0.ne'
  have hlim := (tendsto_const_nhds (x := β / (2 * π))).mul
    (hc.div hslope (mul_pos two_pos hs0).ne')
  have heq : (fun x => β / (2 * π) * ((1 / √(2 * M + x ^ 2)) / (properDist M x / x)))
      =ᶠ[𝓝[>] 0] conicalRatio M β := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [conicalRatio, sqrtF_sub hM hx, div_div_eq_mul_div]
    ring
  have hv : β / (2 * π) * ((1 / √(2 * M)) / (2 * √(2 * M))) = β / (8 * π * M) := by
    have hss : √(2 * M) * √(2 * M) = 2 * M := Real.mul_self_sqrt (by linarith)
    rw [div_div, mul_left_comm, hss]
    field_simp
    ring
  rw [← hv]
  exact hlim.congr' heq

/-- **ER-3 Hawking 溫度**：單位錐角條件（比值極限為 1）成立，若且唯若 `β = 8πM`。
單位錐角條件是沒有錐狀奇點的一階必要條件，所以「→」方向說：視界光滑只可能在 `β = 8πM`。
「←」方向只給出單位錐角條件，**不**給出光滑：充分性（笛卡兒圖下度規分量光滑）本庫未證，
見 `docs/CHAIN_DESIGN.md` §1 X₁。 -/
theorem hawking_beta {M β : ℝ} (hM : 0 < M) :
    UnitConeAngle M β ↔ β = 8 * π * M := by
  have hlim := conicalRatio_tendsto hM β
  have hpos : 0 < 8 * π * M := mul_pos (mul_pos (by norm_num) pi_pos) hM
  constructor
  · intro h
    exact (div_eq_one_iff_eq hpos.ne').mp (tendsto_nhds_unique hlim h)
  · intro h
    subst h
    rwa [div_self hpos.ne'] at hlim

/-- **負控制**：`β = 4πM`（只有 Hawking 值的一半）時，比值極限是 1/2，單位錐角條件不成立。
因為單位錐角條件是光滑的必要條件，這時視界確實有錐狀奇點（錐角是 2π 的一半）。 -/
theorem negctrl_wrong_beta {M : ℝ} (hM : 0 < M) :
    Tendsto (conicalRatio M (4 * π * M)) (𝓝[>] 0) (𝓝 (1 / 2)) ∧
      ¬ UnitConeAngle M (4 * π * M) := by
  have h := conicalRatio_tendsto hM (4 * π * M)
  have hM' : M ≠ 0 := hM.ne'
  have hv : 4 * π * M / (8 * π * M) = 1 / 2 := by
    field_simp
    ring
  rw [hv] at h
  refine ⟨h, fun h1 => ?_⟩
  have := tendsto_nhds_unique h h1
  norm_num at this

/-! ## 收尾：第一定律推出 S = A/4 -/

/-- **收尾（熱力學第一定律）**：若熵 `S(m)` 滿足 `S(0) = 0`、`dS/dm = β(m)`，
而且每個 `m > 0` 的 `β(m)` 都滿足單位錐角條件（ER-3；一階、必要，不是光滑），
則 `S(M) = 4πM²`，正好是 ER-2 喉部面積的四分之一：`S = A/4`。
假設：能量就是質量 `E = M`、第一定律 `dS = dE / T`、`T = 1/β`；沒有任何量子重力輸入。
`S(0) = 0` 是積分常數的選擇，拿掉就不成立（`negctrl_first_law_const`）。
視界光滑（充分性）本庫未證，見 `docs/CHAIN_DESIGN.md` §1 X₁。 -/
theorem first_law_area {S β : ℝ → ℝ} (h0 : S 0 = 0) (hS : ∀ m, HasDerivAt S (β m) m)
    (hβ : ∀ m, 0 < m → UnitConeAngle m (β m)) {M : ℝ} (hM : 0 < M) :
    S M = 4 * π * M ^ 2 ∧ S M = areaIso M (M / 2) / 4 := by
  have hb : ∀ m, 0 < m → β m = 8 * π * m := fun m hm => (hawking_beta hm).mp (hβ m hm)
  have hgd : ∀ m, HasDerivAt (fun m => S m - 4 * π * m ^ 2) (β m - 8 * π * m) m := by
    intro m
    exact ((hS m).sub ((hasDerivAt_pow 2 m).const_mul (4 * π))).congr_deriv (by push_cast; ring)
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun m => S m - 4 * π * m ^ 2)
    (fun m => β m - 8 * π * m) hM (fun m _ => (hgd m).continuousAt.continuousWithinAt)
    (fun m _ => hgd m)
  simp only [hb c hc.1, sub_self, h0, sub_zero] at hc'
  have hSM : S M = 4 * π * M ^ 2 := by
    rw [eq_comm, div_eq_zero_iff] at hc'
    rcases hc' with h | h
    · nlinarith
    · exact absurd h hM.ne'
  refine ⟨hSM, ?_⟩
  rw [hSM, throat_area_eq hM]
  ring

/-- `S(m) = 4πm²` 滿足 `first_law_area` 的所有假設：假設可以同時成立，定理不是空的。 -/
theorem first_law_witness {M : ℝ} (hM : 0 < M) :
    (fun m : ℝ => 4 * π * m ^ 2) 0 = 0 ∧
      (∀ m, HasDerivAt (fun m : ℝ => 4 * π * m ^ 2) (8 * π * m) m) ∧
      UnitConeAngle M (8 * π * M) := by
  refine ⟨by simp, fun m => ?_, (hawking_beta hM).mpr rfl⟩
  exact ((hasDerivAt_pow 2 m).const_mul (4 * π)).congr_deriv (by push_cast; ring)

/-- **負控制：積分常數**。對任何 `c ≠ 0`，`S(m) = 4πm² + c` 配 `β(m) = 8πm`
滿足 `first_law_area` 除 `S(0) = 0` 以外的全部假設（導數是 `β`；每個 `m > 0` 都滿足單位錐角條件），
但 `S(0) ≠ 0`，結論 `S(M) = 4πM²` 也不成立。所以 `S = A/4` 的常數項完全來自 `h0` 這個選擇，
不是從幾何推出來的。 -/
theorem negctrl_first_law_const {c : ℝ} (hc : c ≠ 0) (M : ℝ) :
    (∀ m, HasDerivAt (fun m : ℝ => 4 * π * m ^ 2 + c) (8 * π * m) m) ∧
      (∀ m : ℝ, 0 < m → UnitConeAngle m (8 * π * m)) ∧
      (fun m : ℝ => 4 * π * m ^ 2 + c) 0 ≠ 0 ∧
      (fun m : ℝ => 4 * π * m ^ 2 + c) M ≠ 4 * π * M ^ 2 := by
  refine ⟨fun m => ?_, fun m hm => (hawking_beta hm).mpr rfl, ?_, ?_⟩
  · exact (((hasDerivAt_pow 2 m).const_mul (4 * π)).add_const c).congr_deriv (by push_cast; ring)
  · show 4 * π * 0 ^ 2 + c ≠ 0
    simpa using hc
  · show 4 * π * M ^ 2 + c ≠ 4 * π * M ^ 2
    intro h
    exact hc (by linarith)

end ErEpr
