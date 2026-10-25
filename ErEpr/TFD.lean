import ErEpr.Basic

/-!
# ErEpr.TFD：T2 熱場雙態

有限維熱場雙態（TFD）`|TFD⟩ ∝ Σ_n e^{-βE_n/2} |u_n⟩ ⊗ |ū_n⟩` 的兩側約化態：
* A 側（`ptrB`）恰為 Gibbs 態 `e^{-βH} / tr e^{-βH}`（`ptrB_tfdState`）；
* B 側（`ptrA`）是它的**轉置** `e^{-βHᵀ} / Z`（`ptrA_tfdState`）。
H 非實時兩者不同（σ_y 見證 `gibbs_pauliY_ne_transpose`）。

兩邊**獨立定義**：
* Gibbs 態用冪級數定義的矩陣指數 `NormedSpace.exp`，不經譜分解；
* TFD 振幅用 Hermitian 矩陣的固有分解 `U · diag(e^{-βE_n/2}) · Uᴴ` 建構，不經矩陣指數。
兩者相等由橋接引理 `tfdAmp_mul_conjTranspose` 證明，這是本檔的實質內容。

CHAIN_DESIGN §5.2 的 S1、S3：
* **S1**（`tfdAmp_eq_exp`）：振幅就是 `e^{-(β/2)H}`；另有不經固有分解的第二條路
  `exp_half_mul_conjTranspose`，兩條互驗（`tfdAmp_mul_conjTranspose'`）。負控制 `negctrl_tfdAmp_full_beta`。
* **S3**（`purification_unique_of_isUnit`）：滿秩方陣的純化唯一到一個么正；
  推論 `tfd_purification_unique`、`tfdAmpWrong_eq`（錯誤振幅只差 B 側么正 `U Uᵀ`）。

範圍（引用前請讀）：
* 物理類比是「雙邊（永恆）黑洞 ↔ TFD」。這裡沒有形式化任何時空幾何或全像對偶。
* 有限維、`H` 為 Hermitian、`β` 為任意實數。

設計見 `DESIGN.md` §4。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-! ## Gibbs 態（矩陣指數定義） -/

/-- Gibbs 態 `e^{-βH} / tr e^{-βH}`，用冪級數定義的矩陣指數，不經譜分解。 -/
def gibbs (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  (trace (NormedSpace.exp (-(β : ℂ) • H)))⁻¹ • NormedSpace.exp (-(β : ℂ) • H)

/-- 純量的 `NormedSpace.exp` 與實指數。 -/
theorem nexp_ofReal (x : ℝ) : NormedSpace.exp (x : ℂ) = ((Real.exp x : ℝ) : ℂ) := by
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

omit [DecidableEq ι] in
/-- 逐點的實指數。 -/
theorem nexp_pi_ofReal (f : ι → ℝ) :
    NormedSpace.exp (fun i => (f i : ℂ)) = fun i => ((Real.exp (f i) : ℝ) : ℂ) := by
  rw [Pi.exp_def]
  funext i
  exact nexp_ofReal (f i)

/-- 實對角矩陣的矩陣指數。 -/
theorem exp_neg_smul_diagonal (E : ι → ℝ) (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • diagonal (fun i => (E i : ℂ))) =
      diagonal (fun i => ((Real.exp (-β * E i) : ℝ) : ℂ)) := by
  have hd : (-(β : ℂ)) • (fun i => (E i : ℂ)) = fun i => ((-β * E i : ℝ) : ℂ) := by
    funext i; simp
  rw [← diagonal_smul, hd, Matrix.exp_diagonal, nexp_pi_ofReal]

/-- 實對角 `H` 的 Gibbs 態就是教科書的 Boltzmann 權重。這條確認 `gibbs` 的定義是對的。 -/
theorem gibbs_diagonal_real (E : ι → ℝ) (β : ℝ) :
    gibbs (diagonal (fun i => (E i : ℂ))) β =
      diagonal (fun i => ((Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j) : ℝ) : ℂ)) := by
  rw [gibbs, exp_neg_smul_diagonal, trace_diagonal, ← diagonal_smul]
  congr 1
  funext i
  simp [div_eq_inv_mul]

/-! ## 由振幅矩陣得到的純態 -/

/-- 振幅矩陣 `M` 對應的純態 `|vec M⟩⟨vec M| / ‖vec M‖²`，其中 `‖vec M‖² = tr(M Mᴴ)`。 -/
def pureOf (M : Matrix ι κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  (trace (M * Mᴴ))⁻¹ • vecMulVec (vecOf M) (star (vecOf M))

omit [DecidableEq ι] in
theorem ptrB_pureOf (M : Matrix ι κ ℂ) :
    ptrB (pureOf M) = (trace (M * Mᴴ))⁻¹ • (M * Mᴴ) := by
  rw [pureOf, ptrB_smul, ptrB_pure]

omit [DecidableEq ι] in
theorem ptrA_pureOf (M : Matrix ι κ ℂ) :
    ptrA (pureOf M) = (trace (M * Mᴴ))⁻¹ • (Mᴴ * M)ᵀ := by
  rw [pureOf, ptrA_smul, ptrA_pure]

omit [DecidableEq ι] in
/-- 歸一化：`tr(M Mᴴ) ≠ 0` 時 `pureOf M` 的跡是 1。 -/
theorem trace_pureOf (M : Matrix ι κ ℂ) (h : trace (M * Mᴴ) ≠ 0) : trace (pureOf M) = 1 := by
  rw [← trace_ptrB (pureOf M), ptrB_pureOf, trace_smul, smul_eq_mul, inv_mul_cancel₀ h]

/-! ## 么正共軛下的對角矩陣 -/

theorem conj_diag_mul_conj_diag (U : Matrix ι ι ℂ) (hU : star U * U = 1) (d e : ι → ℂ) :
    U * diagonal d * star U * (U * diagonal e * star U) =
      U * diagonal (fun i => d i * e i) * star U := by
  calc U * diagonal d * star U * (U * diagonal e * star U)
      = U * diagonal d * (star U * U) * diagonal e * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => d i * e i) * star U := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]

theorem conj_diag_conjTranspose (U : Matrix ι ι ℂ) (d : ι → ℂ) :
    (U * diagonal d * star U)ᴴ = U * diagonal (star d) * star U := by
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]

/-- `conj_diag_mul_conj_diag` 的一般版：左右可以是不同的矩陣，只要中間 `star Y * Y = 1`。 -/
theorem conj_diag_mul_conj_diag' (X Y Z : Matrix ι ι ℂ) (hY : star Y * Y = 1) (d e : ι → ℂ) :
    X * diagonal d * star Y * (Y * diagonal e * star Z) =
      X * diagonal (fun i => d i * e i) * star Z := by
  calc X * diagonal d * star Y * (Y * diagonal e * star Z)
      = X * diagonal d * (star Y * Y) * diagonal e * star Z := by
        simp only [Matrix.mul_assoc]
    _ = X * diagonal (fun i => d i * e i) * star Z := by
        rw [hY, Matrix.mul_one, Matrix.mul_assoc X, diagonal_mul_diagonal]

theorem conj_diag_conjTranspose' (X Y : Matrix ι ι ℂ) (d : ι → ℂ) :
    (X * diagonal d * star Y)ᴴ = Y * diagonal (star d) * star X := by
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- `(A ⊗ B) vec M = vec (A M Bᵀ)`。 -/
theorem kron_mulVec_vecOf (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (M : Matrix ι κ ℂ) :
    (A ⊗ₖ B) *ᵥ vecOf M = vecOf (A * M * Bᵀ) := by
  ext ⟨i, k⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, kroneckerMap_apply, vecOf_apply,
    mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 右乘 `W` 攤平後只作用在 B 側：`vec (M W) = (1 ⊗ Wᵀ) vec M`（`kron_mulVec_vecOf` 取 `A = 1`）。 -/
theorem vecOf_mul (M : Matrix ι κ ℂ) (W : Matrix κ κ ℂ) :
    vecOf (M * W) = ((1 : Matrix ι ι ℂ) ⊗ₖ Wᵀ) *ᵥ vecOf M := by
  rw [kron_mulVec_vecOf, transpose_transpose, Matrix.one_mul]

/-! ## 固有分解 -/

variable {H : Matrix ι ι ℂ}

/-- 固有向量么正矩陣（第 n 行是第 n 個固有向量）。 -/
abbrev eigU (hH : H.IsHermitian) : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)

theorem eigU_star_mul (hH : H.IsHermitian) : star (eigU hH) * eigU hH = 1 :=
  Unitary.coe_star_mul_self _

theorem eigU_mul_star (hH : H.IsHermitian) : eigU hH * star (eigU hH) = 1 :=
  Unitary.coe_mul_star_self _

/-- 譜分解：`H = U · diag(E) · Uᴴ`。 -/
theorem eigU_spectral (hH : H.IsHermitian) :
    H = eigU hH * diagonal (fun n => (hH.eigenvalues n : ℂ)) * star (eigU hH) := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- 矩陣指數在固有基底下：`exp(-βH) = U · diag(e^{-βE_n}) · Uᴴ`。 -/
theorem exp_neg_smul_eigen (hH : H.IsHermitian) (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • H) =
      eigU hH * diagonal (fun n => ((Real.exp (-β * hH.eigenvalues n) : ℝ) : ℂ)) *
        star (eigU hH) := by
  have hinv : (eigU hH)⁻¹ = star (eigU hH) := inv_eq_right_inv (eigU_mul_star hH)
  have hd : (fun n => ((-β * hH.eigenvalues n : ℝ) : ℂ)) =
      (-(β : ℂ)) • fun n => (hH.eigenvalues n : ℂ) := by
    funext n; simp
  have hH' : -(β : ℂ) • H =
      eigU hH * diagonal (fun n => ((-β * hH.eigenvalues n : ℝ) : ℂ)) * (eigU hH)⁻¹ := by
    conv_lhs => rw [eigU_spectral hH]
    rw [hinv, hd, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hH', Matrix.exp_conj _ _ Unitary.isUnit_coe, Matrix.exp_diagonal, nexp_pi_ofReal, hinv]

/-- 配分函數不為零（需要 `ι` 非空；空的時候一切都是零矩陣）。 -/
theorem trace_exp_neg_smul_ne_zero [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    trace (NormedSpace.exp (-(β : ℂ) • H)) ≠ 0 := by
  rw [exp_neg_smul_eigen hH β, trace_mul_cycle, eigU_star_mul, Matrix.one_mul, trace_diagonal,
    ← Complex.ofReal_sum]
  exact Complex.ofReal_ne_zero.mpr
    (Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-! ## TFD 態 -/

/-- TFD 振幅 `U · diag(e^{-βE_n/2}) · Uᴴ = Σ_n e^{-βE_n/2} |u_n⟩⟨u_n|`：由固有分解建構，不經矩陣指數。
`vec` 之後是 `Σ_n e^{-βE_n/2} |u_n⟩ ⊗ |ū_n⟩`，右側自動是複共軛。 -/
def tfdAmp (hH : H.IsHermitian) (β : ℝ) : Matrix ι ι ℂ :=
  eigU hH * diagonal (fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ)) *
    star (eigU hH)

/-- TFD 態（密度矩陣）。 -/
def tfdState (hH : H.IsHermitian) (β : ℝ) : Matrix (ι × ι) (ι × ι) ℂ :=
  pureOf (tfdAmp hH β)

/-- 振幅係數是實數。 -/
theorem amp_star (hH : H.IsHermitian) (β : ℝ) :
    star (fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ)) =
      fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ) := by
  funext n; simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- 振幅係數的平方是 Boltzmann 權重。 -/
theorem amp_sq (hH : H.IsHermitian) (β : ℝ) :
    (fun i => ((Real.exp (-β * hH.eigenvalues i / 2) : ℝ) : ℂ) *
      ((Real.exp (-β * hH.eigenvalues i / 2) : ℝ) : ℂ)) =
      fun i => ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ) := by
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- **u ⊗ ū**：TFD 振幅攤平後是 `Σ_n e^{-βE_n/2} u_n ⊗ ū_n`，
其中 `eigU hH i n = eigenvectorBasis n i`（mathlib 的 `eigenvectorUnitary_apply`，定義上相等）。 -/
theorem vecOf_tfdAmp (hH : H.IsHermitian) (β : ℝ) (i k : ι) :
    vecOf (tfdAmp hH β) (i, k) =
      ∑ n, ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ) *
        (eigU hH i n * star (eigU hH k n)) := by
  rw [vecOf_apply, tfdAmp, mul_apply]
  simp only [mul_diagonal, star_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem tfdAmp_conjTranspose (hH : H.IsHermitian) (β : ℝ) :
    (tfdAmp hH β)ᴴ = tfdAmp hH β := by
  have hd : star (fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ)) =
      fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ) := by
    funext n; simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [tfdAmp, conj_diag_conjTranspose, hd]

/-- **橋接引理**：`tfdAmp · tfdAmpᴴ = exp(-βH)`。
左邊來自固有分解，右邊是冪級數定義的矩陣指數。 -/
theorem tfdAmp_mul_conjTranspose (hH : H.IsHermitian) (β : ℝ) :
    tfdAmp hH β * (tfdAmp hH β)ᴴ = NormedSpace.exp (-(β : ℂ) • H) := by
  have hsq : (fun i => ((Real.exp (-β * hH.eigenvalues i / 2) : ℝ) : ℂ) *
      ((Real.exp (-β * hH.eigenvalues i / 2) : ℝ) : ℂ)) =
      fun i => ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [tfdAmp_conjTranspose, exp_neg_smul_eigen hH β, tfdAmp,
    conj_diag_mul_conj_diag _ (eigU_star_mul hH), hsq]

/-! ## S1：歐氏準備（CHAIN_DESIGN §5.2） -/

/-- **S1**：TFD 振幅就是歐氏半程演化 `e^{-(β/2)H}`（冪級數定義的矩陣指數）。
左邊由固有分解建構，右邊不經譜分解；兩者由 `exp_neg_smul_eigen` 接起來。
物理讀法（只在說明文字裡）：TFD 由歐氏路徑積分的半週期 `β/2` 準備。 -/
theorem tfdAmp_eq_exp (hH : H.IsHermitian) (β : ℝ) :
    tfdAmp hH β = NormedSpace.exp (-((β / 2 : ℝ) : ℂ) • H) := by
  have hd : (fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ)) =
      fun n => ((Real.exp (-(β / 2) * hH.eigenvalues n) : ℝ) : ℂ) := by
    funext n
    congr 2
    ring
  rw [tfdAmp, hd, exp_neg_smul_eigen hH (β / 2)]

/-- **S1 第二條路**（不經固有分解）：`A := e^{-(β/2)H}` 滿足 `A Aᴴ = e^{-βH}`。
只用 `Matrix.exp_conjTranspose`（`H` Hermitian ⇒ `Aᴴ = A`）與 `Matrix.exp_add_of_commute`。 -/
theorem exp_half_mul_conjTranspose (hH : H.IsHermitian) (β : ℝ) :
    NormedSpace.exp (-((β / 2 : ℝ) : ℂ) • H) * (NormedSpace.exp (-((β / 2 : ℝ) : ℂ) • H))ᴴ =
      NormedSpace.exp (-(β : ℂ) • H) := by
  have hA : (-((β / 2 : ℝ) : ℂ) • H)ᴴ = -((β / 2 : ℝ) : ℂ) • H := by
    simp only [conjTranspose_smul, hH.eq, star_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((β / 2 : ℝ) : ℂ) • H) (-((β / 2 : ℝ) : ℂ) • H) := Commute.refl _
  have hsum : -((β / 2 : ℝ) : ℂ) • H + -((β / 2 : ℝ) : ℂ) • H = -(β : ℂ) • H := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, hsum]

/-- **交叉檢查**：橋接引理 `tfdAmp_mul_conjTranspose` 的第二個證明，
走 S1 的兩條路（`tfdAmp_eq_exp` 接 `exp_half_mul_conjTranspose`），與原證明互驗。 -/
theorem tfdAmp_mul_conjTranspose' (hH : H.IsHermitian) (β : ℝ) :
    tfdAmp hH β * (tfdAmp hH β)ᴴ = NormedSpace.exp (-(β : ℂ) • H) := by
  rw [tfdAmp_eq_exp hH β, exp_half_mul_conjTranspose hH β]

/-- TFD 振幅可逆（矩陣指數恆可逆，`Matrix.isUnit_exp`）。 -/
theorem tfdAmp_isUnit (hH : H.IsHermitian) (β : ℝ) : IsUnit (tfdAmp hH β) := by
  rw [tfdAmp_eq_exp hH β]
  exact Matrix.isUnit_exp _

/-! ## S3：純化唯一（滿秩方陣） -/

/-- **S3 純化唯一（滿秩方陣）**：`M` 可逆且 `N Nᴴ = M Mᴴ`，則存在 `W` 使 `W Wᴴ = 1` 且 `N = M W`
（取 `W := M⁻¹ N`）。
範圍：只做方陣且 `M` 可逆的情形。一般（非方陣或秩虧）的 Uhlmann 定理需要極分解，
mathlib 沒有，本庫**不做**。注意：拿掉 `IsUnit M` 之後的方陣陳述其實仍為真（極分解），
只是這裡的證明路線用到可逆。 -/
theorem purification_unique_of_isUnit {M N : Matrix ι ι ℂ} (hM : IsUnit M)
    (h : N * Nᴴ = M * Mᴴ) : ∃ W : Matrix ι ι ℂ, W * Wᴴ = 1 ∧ N = M * W := by
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  refine ⟨M⁻¹ * N, ?_, (mul_nonsing_inv_cancel_left M N hd).symm⟩
  rw [conjTranspose_mul]
  calc M⁻¹ * N * (Nᴴ * (M⁻¹)ᴴ) = M⁻¹ * (N * Nᴴ) * (M⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
    _ = M⁻¹ * (M * Mᴴ) * (M⁻¹)ᴴ := by rw [h]
    _ = (M⁻¹ * M)ᴴ := by rw [nonsing_inv_mul_cancel_left M Mᴴ hd, conjTranspose_mul]
    _ = 1 := by rw [nonsing_inv_mul M hd, conjTranspose_one]

/-- **S3 × T2**：任何滿足 `N Nᴴ = e^{-βH}` 的振幅 `N`（A 側約化態是 Gibbs 態的純化），
都等於 TFD 振幅乘上一個么正 `W`：`N = tfdAmp · W`。攤平後 `W` 只作用在 B 側（`vecOf_mul`）。 -/
theorem tfd_purification_unique (hH : H.IsHermitian) (β : ℝ) {N : Matrix ι ι ℂ}
    (hN : N * Nᴴ = NormedSpace.exp (-(β : ℂ) • H)) :
    ∃ W : Matrix ι ι ℂ, W * Wᴴ = 1 ∧ N = tfdAmp hH β * W :=
  purification_unique_of_isUnit (tfdAmp_isUnit hH β)
    (hN.trans (tfdAmp_mul_conjTranspose hH β).symm)

/-- **T2a**：TFD 的 A 側約化態是 Gibbs 態。 -/
theorem ptrB_tfdState (hH : H.IsHermitian) (β : ℝ) : ptrB (tfdState hH β) = gibbs H β := by
  rw [tfdState, ptrB_pureOf, tfdAmp_mul_conjTranspose, gibbs]

/-- **T2b**：TFD 的 B 側約化態是 Gibbs 態的**轉置**（不是 Gibbs 態本身，見 T2c）。 -/
theorem ptrA_tfdState (hH : H.IsHermitian) (β : ℝ) :
    ptrA (tfdState hH β) = (gibbs H β)ᵀ := by
  have hM : (tfdAmp hH β)ᴴ * tfdAmp hH β = tfdAmp hH β * (tfdAmp hH β)ᴴ := by
    rw [tfdAmp_conjTranspose]
  rw [tfdState, ptrA_pureOf, hM, tfdAmp_mul_conjTranspose, gibbs, transpose_smul]

/-- TFD 態的跡是 1：歸一化真的成立，T2a／T2b 不是「0 = 0」。 -/
theorem trace_tfdState [Nonempty ι] (hH : H.IsHermitian) (β : ℝ) :
    trace (tfdState hH β) = 1 :=
  trace_pureOf _ (by rw [tfdAmp_mul_conjTranspose]; exact trace_exp_neg_smul_ne_zero hH β)

/-! ## 見證 T2c：轉置陷阱（σ_y） -/

/-- Pauli Y：複的 Hermitian 矩陣，`σ_yᵀ = -σ_y`。 -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

/-- 對角化 σ_y 的矩陣：行是固有向量 `(1, i)`（固有值 1）與 `(1, -i)`（固有值 -1）。 -/
def Vy : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; Complex.I, -Complex.I]

def VyInv : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, -Complex.I / 2; 1 / 2, Complex.I / 2]

theorem Vy_mul_VyInv : Vy * VyInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ext_iff, Vy, VyInv, mul_apply, Fin.sum_univ_two] <;> norm_num

theorem VyInv_mul_Vy : VyInv * Vy = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ext_iff, Vy, VyInv, mul_apply, Fin.sum_univ_two] <;> norm_num

theorem Vy_isUnit : IsUnit Vy := ⟨⟨Vy, VyInv, Vy_mul_VyInv, VyInv_mul_Vy⟩, rfl⟩

theorem Vy_inv : Vy⁻¹ = VyInv := inv_eq_right_inv Vy_mul_VyInv

/-- `Vy · diag(a, b) · Vy⁻¹` 的閉式。 -/
theorem Vy_diag_VyInv (a b : ℝ) :
    Vy * diagonal (fun i => ((![a, b] i : ℝ) : ℂ)) * VyInv =
      !![(((a + b) / 2 : ℝ) : ℂ), Complex.I * (((b - a) / 2 : ℝ) : ℂ);
        Complex.I * (((a - b) / 2 : ℝ) : ℂ), (((a + b) / 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> refine Complex.ext ?_ ?_ <;>
    simp [Vy, VyInv, mul_apply, Fin.sum_univ_two, vecMul_diagonal] <;> ring

theorem neg_smul_pauliY (β : ℝ) :
    -(β : ℂ) • pauliY = Vy * diagonal (fun i => ((![-β, β] i : ℝ) : ℂ)) * Vy⁻¹ := by
  rw [Vy_inv, Vy_diag_VyInv]
  ext i j
  fin_cases i <;> fin_cases j <;> refine Complex.ext ?_ ?_ <;> simp [pauliY]
  ring

/-- `exp(-βσ_y) = Vy · diag(e^{β}, e^{-β})… `：固有值 1 對應 `e^{-β}`，-1 對應 `e^{β}`。 -/
theorem exp_neg_smul_pauliY (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • pauliY) =
      Vy * diagonal (fun i => ((Real.exp (![-β, β] i) : ℝ) : ℂ)) * VyInv := by
  rw [neg_smul_pauliY, Matrix.exp_conj _ _ Vy_isUnit, Matrix.exp_diagonal, nexp_pi_ofReal, Vy_inv]

theorem exp_pauliY_01 (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • pauliY) 0 1 =
      Complex.I * (((Real.exp β - Real.exp (-β)) / 2 : ℝ) : ℂ) := by
  have hf : (fun i => ((Real.exp (![-β, β] i) : ℝ) : ℂ)) =
      fun i => ((![Real.exp (-β), Real.exp β] i : ℝ) : ℂ) := by
    funext i; fin_cases i <;> rfl
  rw [exp_neg_smul_pauliY, hf, Vy_diag_VyInv]
  rfl

theorem exp_pauliY_10 (β : ℝ) :
    NormedSpace.exp (-(β : ℂ) • pauliY) 1 0 =
      Complex.I * (((Real.exp (-β) - Real.exp β) / 2 : ℝ) : ℂ) := by
  have hf : (fun i => ((Real.exp (![-β, β] i) : ℝ) : ℂ)) =
      fun i => ((![Real.exp (-β), Real.exp β] i : ℝ) : ℂ) := by
    funext i; fin_cases i <;> rfl
  rw [exp_neg_smul_pauliY, hf, Vy_diag_VyInv]
  rfl

/-- **T2c**：β ≠ 0 時，σ_y 的 Gibbs 態不對稱，所以不等於自己的轉置。
配合 T2b：「TFD 兩側的約化態都是 Gibbs 態」這個說法是錯的。 -/
theorem gibbs_pauliY_ne_transpose {β : ℝ} (hβ : β ≠ 0) :
    gibbs pauliY β ≠ (gibbs pauliY β)ᵀ := by
  intro h
  have hZ : trace (NormedSpace.exp (-(β : ℂ) • pauliY)) ≠ 0 :=
    trace_exp_neg_smul_ne_zero pauliY_isHermitian β
  have h01 := congrFun (congrFun h 0) 1
  rw [transpose_apply, gibbs, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    at h01
  have h01' := mul_left_cancel₀ (inv_ne_zero hZ) h01
  rw [exp_pauliY_01, exp_pauliY_10] at h01'
  have h3 : (Real.exp β - Real.exp (-β)) / 2 = (Real.exp (-β) - Real.exp β) / 2 :=
    Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero h01')
  have hb : Real.exp β = Real.exp (-β) := by linarith
  exact hβ (by linarith [Real.exp_eq_exp.mp hb])

/-- **N5**：σ_y 下，「B 側約化態也是 Gibbs 態」可證偽。 -/
theorem negctrl_ptrA_ne_gibbs {β : ℝ} (hβ : β ≠ 0) :
    ptrA (tfdState pauliY_isHermitian β) ≠ gibbs pauliY β := by
  rw [ptrA_tfdState]
  exact fun h => gibbs_pauliY_ne_transpose hβ h.symm

/-! ## T2d：boost 不變性 -/

/-- 振幅與 `H` 交換（兩者在同一組固有基底下都是對角的）。 -/
theorem commute_tfdAmp (hH : H.IsHermitian) (β : ℝ) : H * tfdAmp hH β = tfdAmp hH β * H := by
  have e := eigU_spectral hH
  calc H * tfdAmp hH β
      = eigU hH * diagonal (fun n => (hH.eigenvalues n : ℂ)) * star (eigU hH) * tfdAmp hH β := by
        rw [← e]
    _ = tfdAmp hH β * (eigU hH * diagonal (fun n => (hH.eigenvalues n : ℂ)) * star (eigU hH)) := by
        rw [tfdAmp, conj_diag_mul_conj_diag _ (eigU_star_mul hH),
          conj_diag_mul_conj_diag _ (eigU_star_mul hH)]
        simp only [mul_comm]
    _ = tfdAmp hH β * H := by rw [← e]

/-- **T2d boost 不變性**：`(H ⊗ 1 - 1 ⊗ Hᵀ)|TFD⟩ = 0`。
物理類比是 Kruskal boost 對稱（左右兩側的時間反向流動）；這裡只是矩陣恆等式。
注意：這條對**每一個** β 都成立，β = 0（Bell 型態）也成立，所以它**不**挑出溫度；
見 `boost_invariant_iff_commute`。 -/
theorem tfd_boost_invariant (hH : H.IsHermitian) (β : ℝ) :
    (H ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Hᵀ) *ᵥ vecOf (tfdAmp hH β) = 0 := by
  rw [sub_mulVec, kron_mulVec_vecOf, kron_mulVec_vecOf, transpose_one, transpose_transpose,
    Matrix.mul_one, Matrix.one_mul, commute_tfdAmp, sub_self]

/-- boost 生成元作用在攤平的振幅上：`(H ⊗ 1 - 1 ⊗ Hᵀ) vec M = vec (H M - M H)`。 -/
theorem boost_mulVec_vecOf (H M : Matrix ι ι ℂ) :
    (H ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Hᵀ) *ᵥ vecOf M = vecOf (H * M - M * H) := by
  rw [sub_mulVec, kron_mulVec_vecOf, kron_mulVec_vecOf, transpose_one, transpose_transpose,
    Matrix.mul_one, Matrix.one_mul]
  ext ⟨i, k⟩
  simp only [Pi.sub_apply, vecOf_apply, Matrix.sub_apply]

/-- **T2d 的真正內容**：振幅 `M` 的 boost 不變性，**等價於** `M` 與 `H` 交換。
這個條件跟 β 無關：任何 `H` 的函數都滿足它（`tfdAmp hH β` 對每個 β 都是），
Bell 型態的振幅 `1` 也滿足它（`boost_invariant_one`）。
所以 boost 不變性**不能**當作字典「溫度」那一行的連結：它不決定 β。 -/
theorem boost_invariant_iff_commute (H M : Matrix ι ι ℂ) :
    (H ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Hᵀ) *ᵥ vecOf M = 0 ↔ H * M = M * H := by
  rw [boost_mulVec_vecOf]
  constructor
  · intro h
    ext i k
    have hik := congrFun h (i, k)
    simp only [vecOf_apply, Pi.zero_apply, Matrix.sub_apply] at hik
    exact sub_eq_zero.mp hik
  · intro h
    rw [h, sub_self]
    rfl

/-- Bell 型態（未歸一化的最大糾纏振幅 `1`）對**任何** `H` 都是 boost 不變的，`H` 不必 Hermitian。 -/
theorem boost_invariant_one (H : Matrix ι ι ℂ) :
    (H ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Hᵀ) *ᵥ vecOf (1 : Matrix ι ι ℂ) = 0 :=
  (boost_invariant_iff_commute H 1).mpr (by rw [Matrix.mul_one, Matrix.one_mul])

/-- β = 0 時 TFD 振幅就是 `1`（Bell 型態）。 -/
theorem tfdAmp_zero (hH : H.IsHermitian) : tfdAmp hH 0 = 1 := by
  have h1 : (fun n => ((Real.exp (-(0 : ℝ) * hH.eigenvalues n / 2) : ℝ) : ℂ)) = fun _ => 1 := by
    funext n
    simp
  rw [tfdAmp, h1, diagonal_one, Matrix.mul_one, eigU_mul_star]

/-- **T2d 與 β 無關**：β = 0 的 TFD（就是 Bell 型態 `1`）照樣 boost 不變。
boost 不變性等價於振幅與 `H` 交換（`boost_invariant_iff_commute`），不依賴 β，
**不能**當作溫度那一行的連結。 -/
theorem tfd_boost_invariant_zero (hH : H.IsHermitian) :
    tfdAmp hH 0 = 1 ∧
      (H ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Hᵀ) *ᵥ vecOf (tfdAmp hH 0) = 0 :=
  ⟨tfdAmp_zero hH, tfd_boost_invariant hH 0⟩

/-! ## 負控制：右側少了共軛（u ⊗ u）的錯誤 TFD

這組負控制取代原本的 R4 演習。R4 只顯示「改壞後證明跑不過」，這裡是正面證明：
錯誤振幅照樣通過 T2a，所以單靠 T2a 抓不到這個錯；T2b 在 σ_y 下會失敗，抓得到。 -/

/-- 錯誤的 TFD 振幅：右側用 `Uᵀ`，也就是 `Σ e^{-βE/2} u_n ⊗ u_n`（少了複共軛）。 -/
def tfdAmpWrong (hH : H.IsHermitian) (β : ℝ) : Matrix ι ι ℂ :=
  eigU hH * diagonal (fun n => ((Real.exp (-β * hH.eigenvalues n / 2) : ℝ) : ℂ)) * (eigU hH)ᵀ

theorem eigU_transpose_eq (hH : H.IsHermitian) : (eigU hH)ᵀ = star ((eigU hH).map star) := by
  ext i j
  simp [star_apply]

theorem mapStar_transpose (hH : H.IsHermitian) : ((eigU hH).map star)ᵀ = star (eigU hH) := rfl

theorem star_mapStar_mul (hH : H.IsHermitian) :
    star ((eigU hH).map star) * (eigU hH).map star = 1 := by
  rw [← eigU_transpose_eq]
  have h := congrArg transpose (eigU_star_mul hH)
  rw [transpose_mul, transpose_one] at h
  exact h

theorem wrong_mul_conjTranspose (hH : H.IsHermitian) (β : ℝ) :
    tfdAmpWrong hH β * (tfdAmpWrong hH β)ᴴ = NormedSpace.exp (-(β : ℂ) • H) := by
  rw [tfdAmpWrong, eigU_transpose_eq, conj_diag_conjTranspose', amp_star,
    conj_diag_mul_conj_diag' _ _ _ (star_mapStar_mul hH), amp_sq, exp_neg_smul_eigen]

theorem wrong_conjTranspose_mul_transpose (hH : H.IsHermitian) (β : ℝ) :
    ((tfdAmpWrong hH β)ᴴ * tfdAmpWrong hH β)ᵀ = NormedSpace.exp (-(β : ℂ) • H) := by
  rw [tfdAmpWrong, eigU_transpose_eq, conj_diag_conjTranspose', amp_star,
    conj_diag_mul_conj_diag' _ _ _ (eigU_star_mul hH), amp_sq, transpose_mul, transpose_mul,
    diagonal_transpose, ← eigU_transpose_eq, transpose_transpose, mapStar_transpose,
    ← Matrix.mul_assoc, exp_neg_smul_eigen]

/-- 錯誤振幅的 A 側約化態照樣是 Gibbs 態：T2a 抓不到這個錯。 -/
theorem ptrB_pureOf_wrong (hH : H.IsHermitian) (β : ℝ) :
    ptrB (pureOf (tfdAmpWrong hH β)) = gibbs H β := by
  rw [ptrB_pureOf, wrong_mul_conjTranspose, gibbs]

/-- 錯誤振幅的 B 側約化態也是 Gibbs 態本身（不是轉置）。 -/
theorem ptrA_pureOf_wrong (hH : H.IsHermitian) (β : ℝ) :
    ptrA (pureOf (tfdAmpWrong hH β)) = gibbs H β := by
  rw [ptrA_pureOf, wrong_conjTranspose_mul_transpose, wrong_mul_conjTranspose, gibbs]

/-- **負控制（取代 R4）**：σ_y 下，錯誤振幅通過 T2a，卻違反 T2b。 -/
theorem negctrl_wrong_amplitude {β : ℝ} (hβ : β ≠ 0) :
    ptrB (pureOf (tfdAmpWrong pauliY_isHermitian β)) = gibbs pauliY β ∧
      ptrA (pureOf (tfdAmpWrong pauliY_isHermitian β)) ≠ (gibbs pauliY β)ᵀ := by
  refine ⟨ptrB_pureOf_wrong _ _, ?_⟩
  rw [ptrA_pureOf_wrong]
  exact gibbs_pauliY_ne_transpose hβ

/-- **S3 推論**：錯誤振幅 = 正確振幅 · `(U Uᵀ)`。
`U Uᵀ` 么正（`eigU_mul_transpose_unitary`），攤平後只作用在 B 側（`vecOf_tfdAmpWrong`）。
這就是為什麼 T2a 看不見 B 側么正、T2b 才釘住它：A 側約化態對 B 側么正不變，
B 側約化態則被它共軛（σ_y 下可見，`negctrl_wrong_amplitude`）。 -/
theorem tfdAmpWrong_eq (hH : H.IsHermitian) (β : ℝ) :
    tfdAmpWrong hH β = tfdAmp hH β * (eigU hH * (eigU hH)ᵀ) := by
  rw [tfdAmpWrong, tfdAmp, ← Matrix.mul_assoc, Matrix.mul_assoc _ (star (eigU hH)),
    eigU_star_mul, Matrix.mul_one]

/-- `U Uᵀ` 是么正矩陣（`W Wᴴ = 1`）。 -/
theorem eigU_mul_transpose_unitary (hH : H.IsHermitian) :
    eigU hH * (eigU hH)ᵀ * (eigU hH * (eigU hH)ᵀ)ᴴ = 1 := by
  have h1 : (eigU hH)ᵀ * ((eigU hH)ᵀ)ᴴ = 1 := by
    rw [eigU_transpose_eq, ← star_eq_conjTranspose, star_star, star_mapStar_mul]
  rw [conjTranspose_mul, ← star_eq_conjTranspose (eigU hH)]
  calc eigU hH * (eigU hH)ᵀ * (((eigU hH)ᵀ)ᴴ * star (eigU hH))
      = eigU hH * ((eigU hH)ᵀ * ((eigU hH)ᵀ)ᴴ) * star (eigU hH) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, eigU_mul_star]

/-- 錯誤振幅攤平後 = `(1 ⊗ U Uᵀ)` 作用在正確的 TFD 向量上（`(U Uᵀ)ᵀ = U Uᵀ`）。 -/
theorem vecOf_tfdAmpWrong (hH : H.IsHermitian) (β : ℝ) :
    vecOf (tfdAmpWrong hH β) =
      ((1 : Matrix ι ι ℂ) ⊗ₖ (eigU hH * (eigU hH)ᵀ)) *ᵥ vecOf (tfdAmp hH β) := by
  rw [tfdAmpWrong_eq, vecOf_mul, transpose_mul, transpose_transpose]

/-! ## 見證 W 與負控制 N6–N7：實對角 H = diag(0, 1) -/

/-- `H = diag(0, 1)`。 -/
def H2 : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => ((![0, 1] i : ℝ) : ℂ)

theorem H2_isHermitian : H2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H2]

/-- **W**：`β = ln 2` 時 Gibbs 態是 `diag(2/3, 1/3)`。 -/
theorem gibbs_H2_log2 :
    gibbs H2 (Real.log 2) = diagonal fun i => ((![2 / 3, 1 / 3] i : ℝ) : ℂ) := by
  rw [H2, gibbs_diagonal_real]
  congr 1
  funext i
  congr 1
  fin_cases i <;> simp [Fin.sum_univ_two, Real.exp_neg, Real.exp_log] <;> norm_num

/-- β 取負號：`diag(1/3, 2/3)`。 -/
theorem gibbs_H2_neg_log2 :
    gibbs H2 (-Real.log 2) = diagonal fun i => ((![1 / 3, 2 / 3] i : ℝ) : ℂ) := by
  rw [H2, gibbs_diagonal_real]
  congr 1
  funext i
  congr 1
  fin_cases i <;> simp [Fin.sum_univ_two, Real.exp_log] <;> norm_num

/-- β = ln 4（＝ 振幅漏掉 1/2 時的有效 β）：`diag(4/5, 1/5)`。 -/
theorem gibbs_H2_log4 :
    gibbs H2 (Real.log 4) = diagonal fun i => ((![4 / 5, 1 / 5] i : ℝ) : ℂ) := by
  rw [H2, gibbs_diagonal_real]
  congr 1
  funext i
  congr 1
  fin_cases i <;> simp [Fin.sum_univ_two, Real.exp_neg, Real.exp_log] <;> norm_num

/-- **N6** 把 β 的符號弄反：TFD 的約化態不是 `gibbs H (-β)`。 -/
theorem negctrl_sign_flip :
    ptrB (tfdState H2_isHermitian (Real.log 2)) ≠ gibbs H2 (-Real.log 2) := by
  rw [ptrB_tfdState, gibbs_H2_log2, gibbs_H2_neg_log2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num at h00

/-- **N7** 振幅漏掉 1/2（`e^{-βE}` 而不是 `e^{-βE/2}`）等於把 β 加倍：
`β = ln 2` 時那就是 `tfdAmp` 在 `ln 4`，約化態是 `diag(4/5, 1/5)`，不是 `gibbs H (ln 2)`。 -/
theorem negctrl_missing_half :
    ptrB (tfdState H2_isHermitian (Real.log 4)) ≠ gibbs H2 (Real.log 2) := by
  rw [ptrB_tfdState, gibbs_H2_log4, gibbs_H2_log2]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num at h00

/-- **E1 的正面版**：把 `tfdAmp_eq_exp` 的 `β/2` 改成 `β` 之後的陳述為假：
`H = diag(0, 1)`、`β ≠ 0` 時 `tfdAmp ≠ e^{-βH}`（`(1,1)` 元是 `e^{-β/2}` 對 `e^{-β}`）。 -/
theorem negctrl_tfdAmp_full_beta {β : ℝ} (hβ : β ≠ 0) :
    tfdAmp H2_isHermitian β ≠ NormedSpace.exp (-(β : ℂ) • H2) := by
  rw [tfdAmp_eq_exp, H2, exp_neg_smul_diagonal, exp_neg_smul_diagonal]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  rw [diagonal_apply_eq, diagonal_apply_eq] at h11
  have h2 := Real.exp_injective (Complex.ofReal_injective h11)
  have e1 : (![0, 1] : Fin 2 → ℝ) 1 = 1 := rfl
  rw [e1] at h2
  exact hβ (by linarith)

end

end ErEpr
