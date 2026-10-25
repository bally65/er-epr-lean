import ErEpr.Hawking

/-!
# ErEpr.Charts：ER 側的三張圖接起來（B3：K1、K1′、K2、K4）

同一個 Schwarzschild 幾何的三張座標圖，全部用顯式係數寫，以 `r`（或 `ρ`）為參數證純量恆等式。
不需要 Lambert W（`r` 作為 `UV` 的函數沒有初等閉式；這裡永遠把 `r` 當參數）。

座標約定：
* **Schwarzschild 圖** `(t, r)`：`ds² = −F_S dt² + dr²/F_S + r² dΩ²`，`F_S(r) = 1 − 2M/r`（`FS`）。
* **Kruskal 圖** `(U, V)`：`ds² = −F_K dU dV + r² dΩ²`，`F_K(r) = 32M³ e^{−r/2M} / r`（`FK`）。
  `w := UV` 與 `r` 由 `UV = −kf(r)` 相連，`kf(r) = (r/2M − 1) e^{r/2M}`（`kf`）。
  右外區（`ER.lean` 的 `RightExterior`，`U < 0 < V`）的參數化是
  `U = −√kf(r) e^{−t/4M}`、`V = √kf(r) e^{t/4M}`（`kruskalU`、`kruskalV`），所以 `V/U = −e^{t/2M}`。
* **各向同性圖** `ρ`（t = 0 切片）：`r = ρ + M + M²/4ρ`（`rOfRho`），
  切片度規 `confIso(ρ) (dρ² + ρ² dΩ²)`，`confIso` 是 `ER.lean` 的 `(1 + M/2ρ)⁴`。

內容：
* **K1 三張圖的係數恆等式**
  * `kf` 在 `r > 0` 上嚴格遞增（`kf_strictMonoOn`），`kf(2M) = 0`（`kf_two_M`），符號由 `r − 2M` 決定。
  * `F_K · (d√kf/dr)² = 1/F_S`（`FK_mul_deriv_sqrt_kf`，`r > 2M`）：`−F_K dU dV` 的徑向部分是 `dr²/F_S`。
  * `F_K · kf / 16M² = F_S`（`FK_mul_kf`）：`−F_K dU dV` 的時間部分是 `−F_S dt²`。
  * 曲線層級（`kruskal_pullback`）：沿右外區任一條曲線 `s ↦ (t(s), r(s))`，
    `−F_K U′V′ = −F_S t′² + r′²/F_S`。這是「Kruskal 度規拉回成 Schwarzschild 度規」的完整陳述，
    方向是 `(t, r) ↦ (U, V)`（不是由 `(U, V)` 反解 `t`，那需要對數與商的導數鏈）。
  * 各向同性 ↔ `r`：`F_S(r(ρ)) = ((ρ − M/2)/(ρ + M/2))²`（`FS_rOfRho`）、`dr/dρ = 1 − M²/4ρ²`
    （`hasDerivAt_rOfRho`）、`confIso = (r/ρ)²`（`confIso_eq_rOfRho`），
    所以 `dr²/F_S + r² dΩ² = confIso (dρ² + ρ² dΩ²)`（`iso_radial`、`iso_angular`）。
    ER-2 的面積 `areaIso` 就是 `4πr²`（`areaIso_eq_rOfRho`）。
* **K1′ 反演就是 U ↔ V**：喉部切片的顯式映射 `X(ρ) = (ρ − M/2) e^{r(ρ)/4M} / √(2Mρ)`（`sliceX`）。
  在 t = 0 切片上 `(U, V) = (−X(ρ), X(ρ))`：`ρ > M/2` 落在右外區、`ρ < M/2` 落在左外區、
  `ρ = M/2` 是分叉球 `U = V = 0`（`slice_rightExterior`、`slice_leftExterior`、`sliceX_throat`）；
  `UV = −kf(r(ρ))`（`slice_prod`，由 `X² = kf(r(ρ))`，`sliceX_sq`）。
  * 反演 `ρ ↦ M²/4ρ` 給出 `X ↦ −X`（`sliceX_inv`），也就是 `U ↔ V`（`inversion_swaps_UV`）。
  * 度規：`F_K(r(ρ)) · X′(ρ)² = confIso(ρ)`（`FK_mul_deriv_sliceX_sq`），
    即 `−F_K dU dV` 限制到切片恰為各向同性的 `confIso dρ²`。
  所以 `ER.lean` 的 `inversion_isometry`（係數層級的反演對稱）落到 Kruskal 座標上就是 `U ↔ V`。
* **K2 boost**：`(U, V) ↦ (e^λ U, e^{−λ} V)` 保 `UV`（`boost_preserves_prod`）、保度規（`boost_metric`）、
  保「指向未來的因果向量」（`futureCausal_boost`）、保三個區域（`rightExterior_boost` 等）。
  * 負控制：「指向未來」（`U′ + V′ > 0`）單獨對類空向量**不是** boost 不變的：
    `(3, −2)` 在 λ = −1 之後變成指向過去（`negctrl_boost_spacelike`）。所以 `FutureCausal` 的「因果」不能拿掉。
  * 這是 `TFD.lean` T2d（`tfd_boost_invariant`）在幾何側的對應，但**仍是類比**，不是定理層級的連結：
    T2d 等價於振幅與 H 交換，與 β 無關（`boost_invariant_iff_commute`）。
* **K4 喉部是鞍點**（全用 `kf` 的符號與單調性，不用 Lambert W）：
  * t = 0 切片（`U = −V ≠ 0`）上 `r > 2M`（`r_gt_of_slice`）；穿過內區的對角線（`U = V ≠ 0`）上 `r < 2M`
    （`r_lt_of_timelike`）；分叉球（`U = 0` 或 `V = 0`）上 `r = 2M`（`r_eq_at_bifurcation`）。
  * 球面面積 `4πr²` 是 `w = −UV` 的嚴格遞增函數（`area_lt_area_iff`）；
    沿切片方向 `> 16πM²`、沿時間方向 `< 16πM²`（`area_slice_gt`、`area_timelike_lt`），
    `16πM²` 就是 `ER.lean` 的 `throat_area_eq`。
  * 負控制：未來內區的一點 `(U, V) = (√(e^{1/2}/2), √(e^{1/2}/2))`（M = 1，r = 1），
    面積 `4π < 16π`（`negctrl_interior_area`）。所以 ER-2 的「喉部是極小球面」只在 t = 0 切片上成立，
    在整個時空裡喉部是鞍點，不是極小。

範圍（引用前請讀）：
* 全部是係數層級的純量恆等式與單變數微積分；沒有流形、沒有聯絡、沒有證明這些係數滿足 Einstein 方程。
* 三張圖用的是同一個 `M`，但「它們是同一個流形的三張圖」是座標變換的定義，不是定理：
  這裡證的是「度規係數在變換下互相拉回」，不是流形的建構或整體等距。
* `r(UV)` 的存在（需要 Lambert W）沒有證；所有區域刻畫都以「給定 `r` 滿足 `kf(r) = −UV`」為假設。
-/

namespace ErEpr

open Real

noncomputable section

/-! ## 三張圖的係數 -/

/-- Schwarzschild 圖的係數 `F_S(r) = 1 − 2M/r`：`ds² = −F_S dt² + dr²/F_S + r² dΩ²`。 -/
def FS (M r : ℝ) : ℝ := 1 - 2 * M / r

/-- Kruskal 的 `UV` 與 `r` 的關係：`UV = −kf(r)`，`kf(r) = (r/2M − 1) e^{r/2M}`。 -/
def kf (M r : ℝ) : ℝ := (r / (2 * M) - 1) * exp (r / (2 * M))

/-- Kruskal 圖的係數 `F_K(r) = 32M³ e^{−r/2M} / r`：`ds² = −F_K dU dV + r² dΩ²`。 -/
def FK (M r : ℝ) : ℝ := 32 * M ^ 3 * exp (-(r / (2 * M))) / r

/-- 各向同性半徑 `ρ` 對應的面積半徑 `r = ρ + M + M²/4ρ`。 -/
def rOfRho (M ρ : ℝ) : ℝ := ρ + M + M ^ 2 / (4 * ρ)

/-! ## K1：`kf` 的導數、單調性與符號 -/

/-- `kf` 的導數 `(r/4M²) e^{r/2M}`。 -/
theorem hasDerivAt_kf {M : ℝ} (hM : M ≠ 0) (r : ℝ) :
    HasDerivAt (kf M) (r / (4 * M ^ 2) * exp (r / (2 * M))) r := by
  have h1 : HasDerivAt (fun r : ℝ => r / (2 * M) - 1) (1 / (2 * M)) r :=
    ((hasDerivAt_id' r).div_const (2 * M)).sub_const 1
  have h2 : HasDerivAt (fun r : ℝ => exp (r / (2 * M))) (exp (r / (2 * M)) * (1 / (2 * M))) r :=
    ((hasDerivAt_id' r).div_const (2 * M)).exp
  refine (h1.fun_mul h2).congr_deriv ?_
  field_simp
  ring

/-- **K1** `kf` 在 `r > 0` 上嚴格遞增：在 `r > 0` 上 `w = UV` 唯一決定 `r`（`area_lt_area_iff` 用到）。 -/
theorem kf_strictMonoOn {M : ℝ} (hM : 0 < M) : StrictMonoOn (kf M) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun r _ => (hasDerivAt_kf hM.ne' r).continuousAt.continuousWithinAt) fun r hr => ?_
  rw [interior_Ioi, Set.mem_Ioi] at hr
  rw [(hasDerivAt_kf hM.ne' r).deriv]
  exact mul_pos (div_pos hr (by positivity)) (exp_pos _)

/-- **K1** 視界 `r = 2M` 是 `kf` 的零點：`UV = 0`。 -/
theorem kf_two_M {M : ℝ} (hM : M ≠ 0) : kf M (2 * M) = 0 := by
  rw [kf, div_self (mul_ne_zero two_ne_zero hM), sub_self, zero_mul]

theorem kf_pos_iff {M r : ℝ} (hM : 0 < M) : 0 < kf M r ↔ 2 * M < r := by
  rw [kf, mul_pos_iff_of_pos_right (exp_pos _), sub_pos, one_lt_div (by positivity)]

theorem kf_neg_iff {M r : ℝ} (hM : 0 < M) : kf M r < 0 ↔ r < 2 * M := by
  have h2M : (0 : ℝ) < 2 * M := by positivity
  constructor
  · intro h
    by_contra hr
    rw [not_lt] at hr
    have h0 : 0 ≤ r / (2 * M) - 1 := sub_nonneg.mpr ((one_le_div h2M).mpr hr)
    exact absurd h (not_lt.mpr (mul_nonneg h0 (exp_pos _).le))
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr ((div_lt_one h2M).mpr h)) (exp_pos _)

theorem kf_eq_zero_iff {M r : ℝ} (hM : 0 < M) : kf M r = 0 ↔ r = 2 * M := by
  rw [kf, mul_eq_zero, or_iff_left (exp_pos _).ne', sub_eq_zero,
    div_eq_one_iff_eq (by positivity)]

theorem FS_pos {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) : 0 < FS M r := by
  have hr0 : 0 < r := by linarith
  rw [FS, sub_pos, div_lt_one hr0]
  exact hr

/-! ## K1：Kruskal ↔ Schwarzschild 的係數恆等式 -/

/-- **K1** `F_K · kf / 16M² = F_S`：`−F_K dU dV` 的時間部分是 `−F_S dt²`。 -/
theorem FK_mul_kf {M r : ℝ} (hM : M ≠ 0) (hr : r ≠ 0) :
    FK M r * kf M r / (16 * M ^ 2) = FS M r := by
  have hE : exp (r / (2 * M)) ≠ 0 := (exp_pos _).ne'
  rw [FK, kf, FS, exp_neg]
  field_simp
  ring

/-- `√kf` 在 `r > 2M` 的導數。 -/
theorem hasDerivAt_sqrt_kf {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    HasDerivAt (fun s => √(kf M s)) (r / (4 * M ^ 2) * exp (r / (2 * M)) / (2 * √(kf M r))) r :=
  (hasDerivAt_kf hM.ne' r).sqrt ((kf_pos_iff hM).mpr hr).ne'

/-- `F_K · (d√kf/dr)² = 1/F_S`，導數寫成顯式。 -/
theorem FK_mul_dsqrtkf_sq {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    FK M r * (r / (4 * M ^ 2) * exp (r / (2 * M)) / (2 * √(kf M r))) ^ 2 = 1 / FS M r := by
  have hk : 0 < kf M r := (kf_pos_iff hM).mpr hr
  have hr0 : r ≠ 0 := (show (0 : ℝ) < r by linarith).ne'
  have hrM : r - 2 * M ≠ 0 := (sub_pos.mpr hr).ne'
  have hM0 : M ≠ 0 := hM.ne'
  have hE : exp (r / (2 * M)) ≠ 0 := (exp_pos _).ne'
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hk.le, FK, kf, FS, exp_neg]
  field_simp
  ring

/-- **K1** `F_K · (d√kf/dr)² = 1/F_S`（`r > 2M`）：t = 0 切片 `U = −V = −√kf` 上，
`−F_K dU dV` 限制成 `dr²/F_S`。 -/
theorem FK_mul_deriv_sqrt_kf {M r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    FK M r * deriv (fun s => √(kf M s)) r ^ 2 = 1 / FS M r := by
  rw [(hasDerivAt_sqrt_kf hM hr).deriv]
  exact FK_mul_dsqrtkf_sq hM hr

/-! ## K1：曲線層級，Kruskal 度規拉回成 Schwarzschild 度規 -/

/-- 右外區的 Kruskal 座標 `U = −√kf(r) e^{−t/4M}`。 -/
def kruskalU (M t r : ℝ) : ℝ := -√(kf M r) * exp (-(t / (4 * M)))

/-- 右外區的 Kruskal 座標 `V = √kf(r) e^{t/4M}`。 -/
def kruskalV (M t r : ℝ) : ℝ := √(kf M r) * exp (t / (4 * M))

/-- 保真：`UV = −kf(r)`。 -/
theorem kruskalU_mul_V {M t r : ℝ} (hM : 0 < M) (hr : 2 * M ≤ r) :
    kruskalU M t r * kruskalV M t r = -kf M r := by
  have hk : 0 ≤ kf M r := by
    rcases hr.lt_or_eq with h | h
    · exact ((kf_pos_iff hM).mpr h).le
    · rw [← h, kf_two_M hM.ne']
  have he : exp (-(t / (4 * M))) * exp (t / (4 * M)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [kruskalU, kruskalV]
  calc -√(kf M r) * exp (-(t / (4 * M))) * (√(kf M r) * exp (t / (4 * M)))
      = -(√(kf M r) * √(kf M r)) * (exp (-(t / (4 * M))) * exp (t / (4 * M))) := by ring
    _ = -kf M r := by rw [Real.mul_self_sqrt hk, he, mul_one]

/-- 保真：`V/U = −e^{t/2M}`，所以 `t` 就是 Schwarzschild 時間。 -/
theorem kruskalV_div_U {M t r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    kruskalV M t r / kruskalU M t r = -exp (t / (2 * M)) := by
  have hs : √(kf M r) ≠ 0 := (Real.sqrt_pos.mpr ((kf_pos_iff hM).mpr hr)).ne'
  have he : exp (t / (2 * M)) = exp (t / (4 * M)) * exp (t / (4 * M)) := by
    rw [← exp_add]
    congr 1
    ring
  have hE : exp (t / (4 * M)) ≠ 0 := (exp_pos _).ne'
  rw [kruskalU, kruskalV, exp_neg, he]
  field_simp

/-- 保真：這組參數化落在 `ER.lean` 的右外區。 -/
theorem kruskal_rightExterior {M t r : ℝ} (hM : 0 < M) (hr : 2 * M < r) :
    RightExterior (kruskalU M t r) (kruskalV M t r) := by
  have hs : 0 < √(kf M r) := Real.sqrt_pos.mpr ((kf_pos_iff hM).mpr hr)
  constructor
  · rw [kruskalU, neg_mul]
    exact neg_lt_zero.mpr (mul_pos hs (exp_pos _))
  · exact mul_pos hs (exp_pos _)

/-- **K1 曲線層級**：沿右外區任一條曲線 `s ↦ (t(s), r(s))`，令 `U = kruskalU`、`V = kruskalV`，
則 `−F_K(r) U′ V′ = −F_S(r) t′² + r′²/F_S(r)`。
也就是 Kruskal 度規 `−F_K dU dV` 拉回成 Schwarzschild 度規 `−F_S dt² + dr²/F_S`。 -/
theorem kruskal_pullback {M : ℝ} (hM : 0 < M) {t r : ℝ → ℝ} {t' r' s : ℝ}
    (ht : HasDerivAt t t' s) (hr : HasDerivAt r r' s) (hrs : 2 * M < r s) :
    ∃ U' V', HasDerivAt (fun s => kruskalU M (t s) (r s)) U' s ∧
      HasDerivAt (fun s => kruskalV M (t s) (r s)) V' s ∧
      -FK M (r s) * U' * V' = -FS M (r s) * t' ^ 2 + r' ^ 2 / FS M (r s) := by
  set dk := r s / (4 * M ^ 2) * exp (r s / (2 * M)) / (2 * √(kf M (r s)))
  have ha : HasDerivAt (fun s => √(kf M (r s))) (dk * r') s :=
    (hasDerivAt_sqrt_kf hM hrs).comp s hr
  have hem : HasDerivAt (fun s => exp (-(t s / (4 * M))))
      (exp (-(t s / (4 * M))) * -(t' / (4 * M))) s :=
    ((ht.div_const (4 * M)).fun_neg).exp
  have hep : HasDerivAt (fun s => exp (t s / (4 * M))) (exp (t s / (4 * M)) * (t' / (4 * M))) s :=
    (ht.div_const (4 * M)).exp
  have hU := ha.fun_neg.fun_mul hem
  have hV := ha.fun_mul hep
  refine ⟨_, _, hU, hV, ?_⟩
  have hk : 0 < kf M (r s) := (kf_pos_iff hM).mpr hrs
  have hE : exp (-(t s / (4 * M))) * exp (t s / (4 * M)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have h1 : FK M (r s) * dk ^ 2 = 1 / FS M (r s) := FK_mul_dsqrtkf_sq hM hrs
  have h2 : FK M (r s) * √(kf M (r s)) ^ 2 / (16 * M ^ 2) = FS M (r s) := by
    rw [Real.sq_sqrt hk.le]
    exact FK_mul_kf hM.ne' (show (0 : ℝ) < r s by linarith).ne'
  linear_combination
    (FK M (r s) * ((dk * r') ^ 2 - √(kf M (r s)) ^ 2 * (t' / (4 * M)) ^ 2)) * hE +
      r' ^ 2 * h1 - t' ^ 2 * h2

/-! ## K1：各向同性 ↔ r -/

theorem rOfRho_eq {M ρ : ℝ} (hρ : ρ ≠ 0) : rOfRho M ρ = (ρ + M / 2) ^ 2 / ρ := by
  rw [rOfRho]
  field_simp
  ring

theorem rOfRho_pos {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) : 0 < rOfRho M ρ := by
  rw [rOfRho]
  positivity

/-- 喉部 `ρ = M/2` 對應 `r = 2M`。 -/
theorem rOfRho_throat {M : ℝ} (hM : M ≠ 0) : rOfRho M (M / 2) = 2 * M := by
  rw [rOfRho]
  field_simp
  ring

/-- **K1** `F_S(r(ρ)) = ((ρ − M/2)/(ρ + M/2))²`。 -/
theorem FS_rOfRho {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    FS M (rOfRho M ρ) = ((ρ - M / 2) / (ρ + M / 2)) ^ 2 := by
  rw [FS, rOfRho_eq hρ.ne']
  field_simp
  ring

/-- **K1** `dr/dρ = 1 − M²/4ρ²`。 -/
theorem hasDerivAt_rOfRho {M ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (rOfRho M) (1 - M ^ 2 / (4 * ρ ^ 2)) ρ :=
  (((hasDerivAt_id' ρ).add_const M).add (hasDerivAt_inversion hρ)).congr_deriv (by ring)

/-- **K1** `confIso = (r/ρ)²`：`ER.lean` 的共形因子 `(1 + M/2ρ)⁴` 由 `r(ρ)` 決定。 -/
theorem confIso_eq_rOfRho {M ρ : ℝ} (hρ : ρ ≠ 0) : confIso M ρ = (rOfRho M ρ / ρ) ^ 2 := by
  rw [confIso, rOfRho_eq hρ]
  field_simp

/-- ER-2 的面積就是 `4πr²`。 -/
theorem areaIso_eq_rOfRho {M ρ : ℝ} (hρ : ρ ≠ 0) : areaIso M ρ = 4 * π * rOfRho M ρ ^ 2 := by
  rw [areaIso, confIso_eq_rOfRho hρ]
  field_simp

/-- **K1** 徑向：`(dr/dρ)² = F_S(r(ρ)) · confIso(ρ)`，即 `dr²/F_S = confIso dρ²`（寫成乘積，喉部也成立）。 -/
theorem iso_radial {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    deriv (rOfRho M) ρ ^ 2 = FS M (rOfRho M ρ) * confIso M ρ := by
  rw [(hasDerivAt_rOfRho hρ).deriv, FS_rOfRho hM hρ, confIso]
  field_simp
  ring

/-- **K1** 角向：`r² = confIso · ρ²`。 -/
theorem iso_angular {M ρ : ℝ} (hρ : ρ ≠ 0) : rOfRho M ρ ^ 2 = confIso M ρ * ρ ^ 2 := by
  rw [confIso_eq_rOfRho hρ]
  field_simp

/-! ## K1′：喉部切片的顯式映射，反演就是 U ↔ V -/

/-- t = 0 切片的 Kruskal 座標 `X(ρ) = (ρ − M/2) e^{r(ρ)/4M} / √(2Mρ)`：切片上 `(U, V) = (−X, X)`。 -/
def sliceX (M ρ : ℝ) : ℝ := (ρ - M / 2) * exp (rOfRho M ρ / (4 * M)) / √(2 * M * ρ)

theorem rOfRho_inv {M ρ : ℝ} (hM : M ≠ 0) (hρ : ρ ≠ 0) :
    rOfRho M (M ^ 2 / (4 * ρ)) = rOfRho M ρ := by
  rw [rOfRho, rOfRho]
  field_simp
  ring

/-- **K1′** 反演 `ρ ↦ M²/4ρ` 給出 `X ↦ −X`。 -/
theorem sliceX_inv {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    sliceX M (M ^ 2 / (4 * ρ)) = -sliceX M ρ := by
  have hs : √(2 * M * (M ^ 2 / (4 * ρ))) = M / (2 * ρ) * √(2 * M * ρ) := by
    rw [← Real.sqrt_sq (show 0 ≤ M / (2 * ρ) by positivity), ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    field_simp
    ring
  rw [sliceX, sliceX, rOfRho_inv hM.ne' hρ.ne', hs]
  field_simp
  ring

/-- **K1′** `X² = kf(r(ρ))`：切片上的點 `(−X, X)` 滿足 `UV = −kf(r)`。 -/
theorem sliceX_sq {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) : sliceX M ρ ^ 2 = kf M (rOfRho M ρ) := by
  have hE : exp (rOfRho M ρ / (4 * M)) ^ 2 = exp (rOfRho M ρ / (2 * M)) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  rw [sliceX, div_pow, mul_pow, hE, Real.sq_sqrt (by positivity), kf, rOfRho_eq hρ.ne']
  field_simp
  ring

/-- 導數的代數部分：把 `HasDerivAt.div` 給出的式子化成 `e^{r/4M} (ρ + M/2)³ / (4Mρ² √(2Mρ))`。 -/
theorem sliceX_deriv_alg {M ρ s E : ℝ} (hM : 0 < M) (hρ : 0 < ρ) (hs0 : 0 < s)
    (hs2 : s ^ 2 = 2 * M * ρ) :
    ((1 * E + (ρ - M / 2) * (E * ((1 - M ^ 2 / (4 * ρ ^ 2)) / (4 * M)))) * s -
        (ρ - M / 2) * E * (M / s)) / s ^ 2 =
      E * (ρ + M / 2) ^ 3 / (4 * M * ρ ^ 2 * s) := by
  have hs : s ≠ 0 := hs0.ne'
  have hM0 : M ≠ 0 := hM.ne'
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have step1 : ∀ a b : ℝ, (a * s - b * (M / s)) / s ^ 2 = (a * s ^ 2 - b * M) / s ^ 3 := by
    intro a b
    field_simp
  have step2 : (1 * E + (ρ - M / 2) * (E * ((1 - M ^ 2 / (4 * ρ ^ 2)) / (4 * M)))) * (2 * M * ρ) -
      (ρ - M / 2) * E * M = E * (ρ + M / 2) ^ 3 / (2 * ρ) := by
    field_simp
    ring
  rw [step1, hs2, step2, div_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-2 * ρ * s * E * (ρ + M / 2) ^ 3) * hs2

/-- `X` 的導數 `X′(ρ) = e^{r/4M} (ρ + M/2)³ / (4Mρ² √(2Mρ))`，對所有 `ρ > 0`（含喉部）。 -/
theorem hasDerivAt_sliceX {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    HasDerivAt (sliceX M)
      (exp (rOfRho M ρ / (4 * M)) * (ρ + M / 2) ^ 3 / (4 * M * ρ ^ 2 * √(2 * M * ρ))) ρ := by
  have hs0 : 0 < √(2 * M * ρ) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : √(2 * M * ρ) ^ 2 = 2 * M * ρ := Real.sq_sqrt (by positivity)
  have hlin : HasDerivAt (fun x : ℝ => x - M / 2) 1 ρ := (hasDerivAt_id' ρ).sub_const (M / 2)
  have hE : HasDerivAt (fun x => exp (rOfRho M x / (4 * M)))
      (exp (rOfRho M ρ / (4 * M)) * ((1 - M ^ 2 / (4 * ρ ^ 2)) / (4 * M))) ρ :=
    ((hasDerivAt_rOfRho hρ).div_const (4 * M)).exp
  have hsq : HasDerivAt (fun x : ℝ => √(2 * M * x)) (M / √(2 * M * ρ)) ρ := by
    refine (((hasDerivAt_id' ρ).const_mul (2 * M)).sqrt (by positivity)).congr_deriv ?_
    field_simp
  exact ((hlin.fun_mul hE).fun_div hsq hs0.ne').congr_deriv
    (sliceX_deriv_alg hM hρ hs0 hs2)

/-- **K1′** 度規：`F_K(r(ρ)) · X′(ρ)² = confIso(ρ)`。切片上 `U = −X`、`V = X`，
所以 `−F_K dU dV = F_K X′² dρ² = confIso dρ²`：Kruskal 度規限制到切片就是各向同性度規。 -/
theorem FK_mul_deriv_sliceX_sq {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    FK M (rOfRho M ρ) * deriv (sliceX M) ρ ^ 2 = confIso M ρ := by
  have hs2 : √(2 * M * ρ) ^ 2 = 2 * M * ρ := Real.sq_sqrt (by positivity)
  have hE : exp (rOfRho M ρ / (4 * M)) ^ 2 = exp (rOfRho M ρ / (2 * M)) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  rw [(hasDerivAt_sliceX hM hρ).deriv, div_pow, mul_pow, mul_pow, hE, hs2, FK, exp_neg,
    confIso, rOfRho_eq hρ.ne']
  field_simp
  ring

theorem sliceX_throat (M : ℝ) : sliceX M (M / 2) = 0 := by
  rw [sliceX, sub_self, zero_mul, zero_div]

/-- 切片上 `ρ > M/2` 的一端落在右外區。 -/
theorem slice_rightExterior {M ρ : ℝ} (hM : 0 < M) (hρ : M / 2 < ρ) :
    RightExterior (-sliceX M ρ) (sliceX M ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hX : 0 < sliceX M ρ :=
    div_pos (mul_pos (sub_pos.mpr hρ) (exp_pos _)) (Real.sqrt_pos.mpr (by positivity))
  exact ⟨neg_lt_zero.mpr hX, hX⟩

/-- 切片上 `ρ < M/2` 的一端落在左外區。 -/
theorem slice_leftExterior {M ρ : ℝ} (hM : 0 < M) (hρ0 : 0 < ρ) (hρ : ρ < M / 2) :
    LeftExterior (-sliceX M ρ) (sliceX M ρ) := by
  have hX : sliceX M ρ < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hρ) (exp_pos _))
      (Real.sqrt_pos.mpr (by positivity))
  exact ⟨neg_pos.mpr hX, hX⟩

/-- 切片上的點 `(U, V) = (−X, X)` 滿足 `UV = −kf(r(ρ))`。 -/
theorem slice_prod {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    -sliceX M ρ * sliceX M ρ = -kf M (rOfRho M ρ) := by
  rw [neg_mul, ← pow_two, sliceX_sq hM hρ]

/-- **K1′** 反演交換 U 與 V：`ρ ↦ M²/4ρ` 把切片上的 `(−X, X)` 變成 `(X, −X)`。 -/
theorem inversion_swaps_UV {M ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) :
    (-sliceX M (M ^ 2 / (4 * ρ)), sliceX M (M ^ 2 / (4 * ρ))) = (sliceX M ρ, -sliceX M ρ) := by
  rw [sliceX_inv hM hρ, neg_neg]

/-! ## K2：boost -/

/-- **K2** boost `(U, V) ↦ (e^λ U, e^{−λ} V)` 保 `UV`，所以保 `r`（`kf(r) = −UV`）。 -/
theorem boost_preserves_prod (l U V : ℝ) : exp l * U * (exp (-l) * V) = U * V := by
  calc exp l * U * (exp (-l) * V) = (exp l * exp (-l)) * (U * V) := by ring
    _ = U * V := by rw [← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- **K2** boost 保度規 `−G(UV) dU dV`：對任何係數函數 `G`（例如 `F_K` 寫成 `UV` 的函數）。 -/
theorem boost_metric (G : ℝ → ℝ) (l U V U' V' : ℝ) :
    -G (exp l * U * (exp (-l) * V)) * (exp l * U') * (exp (-l) * V') = -G (U * V) * U' * V' := by
  rw [boost_preserves_prod, mul_assoc (-G (U * V)), boost_preserves_prod, ← mul_assoc]

theorem exp_mul_pos_iff {l x : ℝ} : 0 < exp l * x ↔ 0 < x :=
  mul_pos_iff_of_pos_left (exp_pos l)

theorem exp_mul_neg_iff {l x : ℝ} : exp l * x < 0 ↔ x < 0 := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (not_lt.mpr (mul_nonneg (exp_pos l).le (not_lt.mp hx)))
  · exact mul_neg_of_pos_of_neg (exp_pos l)

theorem futureCausal_boost_of {F A U' V' : ℝ} (l : ℝ) (h : FutureCausal F A U' V') :
    FutureCausal F A (exp l * U') (exp (-l) * V') := by
  obtain ⟨hU, hV⟩ := h.nonneg
  obtain ⟨hF, hA, hc, hf⟩ := h
  refine ⟨hF, hA, ?_, ?_⟩
  · have e : -F * (exp l * U') * (exp (-l) * V') = -F * U' * V' := by
      rw [mul_assoc (-F), boost_preserves_prod, ← mul_assoc]
    rw [e]
    exact hc
  · rcases hU.lt_or_eq with hU' | hU'
    · have h1 := mul_pos (exp_pos l) hU'
      have h2 := mul_nonneg (exp_pos (-l)).le hV
      linarith
    · have hV' : 0 < V' := by linarith
      have h1 := mul_pos (exp_pos (-l)) hV'
      rw [← hU', mul_zero]
      linarith

/-- **K2** boost 保「指向未來的因果向量」：切向量 `(U′, V′) ↦ (e^λ U′, e^{−λ} V′)`。 -/
theorem futureCausal_boost {F A U' V' : ℝ} (l : ℝ) :
    FutureCausal F A (exp l * U') (exp (-l) * V') ↔ FutureCausal F A U' V' := by
  refine ⟨fun h => ?_, futureCausal_boost_of l⟩
  have h' := futureCausal_boost_of (-l) h
  have e1 : exp (-l) * (exp l * U') = U' := by
    rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
  have e2 : exp (-(-l)) * (exp (-l) * V') = V' := by
    rw [neg_neg, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  rwa [e1, e2] at h'

/-- **K2** boost 保右外區。 -/
theorem rightExterior_boost (l U V : ℝ) :
    RightExterior (exp l * U) (exp (-l) * V) ↔ RightExterior U V := by
  rw [RightExterior, RightExterior, exp_mul_neg_iff, exp_mul_pos_iff]

/-- **K2** boost 保左外區。 -/
theorem leftExterior_boost (l U V : ℝ) :
    LeftExterior (exp l * U) (exp (-l) * V) ↔ LeftExterior U V := by
  rw [LeftExterior, LeftExterior, exp_mul_neg_iff, exp_mul_pos_iff]

/-- **K2** boost 保未來內區。 -/
theorem futureInterior_boost (l U V : ℝ) :
    FutureInterior (exp l * U) (exp (-l) * V) ↔ FutureInterior U V := by
  rw [FutureInterior, FutureInterior, exp_mul_pos_iff, exp_mul_pos_iff]

/-- **K2 負控制**：類空向量 `(3, −2)` 滿足 `U′ + V′ > 0`（「指向未來」那一條），
但 λ = −1 的 boost 之後 `e^{−1}·3 + e·(−2) < 0`。所以只有「指向未來」而沒有「因果」，不是 boost 不變的；
`futureCausal_boost` 的內容來自因果條件。 -/
theorem negctrl_boost_spacelike :
    (0 : ℝ) < 3 + (-2) ∧ (∀ F A : ℝ, 0 < F → 0 ≤ A → 0 < -F * 3 * (-2) + A) ∧
      exp (-1) * 3 + exp (-(-1)) * (-2) < 0 := by
  refine ⟨by norm_num, fun F A hF hA => by nlinarith, ?_⟩
  rw [neg_neg]
  have h1 := Real.exp_one_gt_d9
  have h2 : exp (-1) < 1 / 2 := by
    rw [exp_neg, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
    norm_num
    linarith
  linarith

/-! ## K4：喉部是鞍點 -/

/-- **K4** t = 0 切片（`U = −V ≠ 0`）上 `r > 2M`。 -/
theorem r_gt_of_slice {M U V r : ℝ} (hM : 0 < M) (hUV : U = -V) (hU : U ≠ 0)
    (hr : kf M r = -(U * V)) : 2 * M < r := by
  rw [← kf_pos_iff hM, hr, hUV, neg_mul, neg_neg]
  have hV : V ≠ 0 := fun h => hU (by rw [hUV, h, neg_zero])
  exact mul_self_pos.mpr hV

/-- **K4** 穿過內區的對角線（`U = V ≠ 0`）上 `r < 2M`。 -/
theorem r_lt_of_timelike {M U V r : ℝ} (hM : 0 < M) (hUV : U = V) (hU : U ≠ 0)
    (hr : kf M r = -(U * V)) : r < 2 * M := by
  rw [← kf_neg_iff hM, hr, hUV]
  have hV : V ≠ 0 := fun h => hU (by rw [hUV, h])
  exact neg_lt_zero.mpr (mul_self_pos.mpr hV)

/-- **K4** 分叉球（`U = 0` 或 `V = 0`）上 `r = 2M`。 -/
theorem r_eq_at_bifurcation {M U V r : ℝ} (hM : 0 < M) (h : U = 0 ∨ V = 0)
    (hr : kf M r = -(U * V)) : r = 2 * M := by
  rw [← kf_eq_zero_iff hM, hr]
  rcases h with h | h <;> simp [h]

/-- **K4** 面積 `4πr²` 是 `w = −UV` 的嚴格遞增函數（`r > 0`）：用 `kf` 的嚴格單調性。 -/
theorem area_lt_area_iff {M r₁ r₂ U₁ V₁ U₂ V₂ : ℝ} (hM : 0 < M) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hr₁ : kf M r₁ = -(U₁ * V₁)) (hr₂ : kf M r₂ = -(U₂ * V₂)) :
    4 * π * r₁ ^ 2 < 4 * π * r₂ ^ 2 ↔ -(U₁ * V₁) < -(U₂ * V₂) := by
  rw [← hr₁, ← hr₂, (kf_strictMonoOn hM).lt_iff_lt h₁ h₂]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have := mul_self_le_mul_self h₂.le hle
    nlinarith [pi_pos]
  · intro h
    have := mul_self_lt_mul_self h₁.le h
    nlinarith [pi_pos]

/-- **K4** 沿切片方向面積大於喉部：`16πM² = areaIso M (M/2) < 4πr²`（`throat_area_eq`）。 -/
theorem area_slice_gt {M U V r : ℝ} (hM : 0 < M) (hUV : U = -V) (hU : U ≠ 0)
    (hr : kf M r = -(U * V)) : areaIso M (M / 2) < 4 * π * r ^ 2 := by
  have h := r_gt_of_slice hM hUV hU hr
  rw [throat_area_eq hM]
  have h2 : (2 * M) * (2 * M) < r * r := mul_self_lt_mul_self (by positivity) h
  nlinarith [pi_pos]

/-- **K4** 沿時間方向面積小於喉部：`4πr² < areaIso M (M/2) = 16πM²`。 -/
theorem area_timelike_lt {M U V r : ℝ} (hM : 0 < M) (hr0 : 0 < r) (hUV : U = V) (hU : U ≠ 0)
    (hr : kf M r = -(U * V)) : 4 * π * r ^ 2 < areaIso M (M / 2) := by
  have h := r_lt_of_timelike hM hUV hU hr
  rw [throat_area_eq hM]
  have h2 : r * r < (2 * M) * (2 * M) := mul_self_lt_mul_self hr0.le h
  nlinarith [pi_pos]

/-- **K4** 分叉球上面積恰為喉部面積。 -/
theorem area_bifurcation_eq {M U V r : ℝ} (hM : 0 < M) (h : U = 0 ∨ V = 0)
    (hr : kf M r = -(U * V)) : 4 * π * r ^ 2 = areaIso M (M / 2) := by
  rw [r_eq_at_bifurcation hM h hr, throat_area_eq hM]
  ring

/-- **K4 負控制**：M = 1 時未來內區的一點 `(U, V) = (√(e^{1/2}/2), √(e^{1/2}/2))` 的半徑是 `r = 1`
（`kf(1) = −UV`），面積 `4π < 16π = areaIso 1 (1/2)`。
所以 `throat_area_le`（面積 ≥ 16πM²）只在 t = 0 切片上成立；在整個時空裡喉部是鞍點。 -/
theorem negctrl_interior_area :
    FutureInterior (√(exp (1 / 2) / 2)) (√(exp (1 / 2) / 2)) ∧
      kf 1 1 = -(√(exp (1 / 2) / 2) * √(exp (1 / 2) / 2)) ∧
      4 * π * (1 : ℝ) ^ 2 < areaIso 1 (1 / 2) := by
  have hpos : 0 < √(exp (1 / 2) / 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨⟨hpos, hpos⟩, ?_, ?_⟩
  · have e : (1 : ℝ) / (2 * 1) = 1 / 2 := by norm_num
    rw [kf, e, Real.mul_self_sqrt (by positivity)]
    ring
  · rw [throat_area_eq one_pos]
    nlinarith [pi_pos]

end

end ErEpr
