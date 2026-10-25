import ErEpr.Basic

/-!
# ErEpr.NoSignalling：T1 不可通訊

對 B 側施加任何 ℂ-線性、保跡的映射，A 側的約化態都不變。

範圍（引用前請讀）：
* 主定理只用到「保跡」，沒用到完全正性；所以它不刻畫「量子通道」。
  轉置映射保跡但不是完全正，定理照樣適用（`witness_transpose`；「非完全正」本檔沒有證明）。
* 只證邊際不變，沒有證輸出仍是量子態（那需要完全正性）。
* 物理類比是「ER 橋不可穿越」。這裡沒有形式化任何重力或時空幾何。

設計見 `DESIGN.md` §3。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι κ κ' r : Type*} [Fintype ι] [Fintype κ] [Fintype κ'] [Fintype r]

/-! ## 主定理 -/

omit [Fintype ι] in
/-- **T1 不可通訊**：B 側任何 ℂ-線性保跡映射 `Φ`，都不改變 A 側的約化態。 -/
theorem ptrB_idKron (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (hTP : ∀ M, trace (Φ M) = trace M) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ptrB (idKron Φ X) = ptrB X := by
  ext i j
  rw [ptrB_idKron_apply, hTP, ptrB_apply]
  simp [trace]

/-! ## Kraus 形式（推論） -/

/-- `M ↦ Σ_a K_a M K_aᴴ`。不要求保跡。 -/
def sandwich {n : Type*} [Fintype n] (K : r → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun M := ∑ a, K a * M * (K a)ᴴ
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

@[simp] theorem sandwich_apply {n : Type*} [Fintype n] (K : r → Matrix n n ℂ)
    (M : Matrix n n ℂ) : sandwich K M = ∑ a, K a * M * (K a)ᴴ := rfl

/-- `tr (Σ K_a M K_aᴴ) = tr ((Σ K_aᴴ K_a) M)`。 -/
theorem trace_sandwich {n : Type*} [Fintype n] (K : r → Matrix n n ℂ) (M : Matrix n n ℂ) :
    trace (sandwich K M) = trace ((∑ a, (K a)ᴴ * K a) * M) := by
  rw [sandwich_apply, trace_sum, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [trace_mul_comm, ← Matrix.mul_assoc]

/-- 雙體上的 Kraus 作用 `Σ (1 ⊗ K_a) X (1 ⊗ K_a)ᴴ` 就是 `idKron (sandwich K)`。
證法走 F8 唯一性，不需要保跡。 -/
theorem sandwich_one_kron [DecidableEq ι] [DecidableEq κ] (K : r → Matrix κ κ ℂ) :
    sandwich (fun a => (1 : Matrix ι ι ℂ) ⊗ₖ K a) = idKron (ι := ι) (sandwich K) := by
  refine idKron_unique _ _ fun A B => ?_
  simp only [sandwich_apply, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext p q
  simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]

/-- Kraus 族：`Σ K_aᴴ K_a = 1`（保跡）。注意不是 `Σ K_a K_aᴴ = 1`，那是 unital（見 N2）。 -/
structure Kraus (κ r : Type*) [Fintype κ] [Fintype r] [DecidableEq κ] where
  K : r → Matrix κ κ ℂ
  tp : ∑ a, (K a)ᴴ * K a = 1

namespace Kraus

variable [DecidableEq κ]

/-- Kraus 族對應的單體映射。 -/
def toLin (Φ : Kraus κ r) : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ κ ℂ := sandwich Φ.K

theorem trace_toLin (Φ : Kraus κ r) (M : Matrix κ κ ℂ) : trace (Φ.toLin M) = trace M := by
  rw [toLin, trace_sandwich, Φ.tp, Matrix.one_mul]

/-- 雙體上的 Kraus 作用 `X ↦ Σ (1 ⊗ K_a) X (1 ⊗ K_a)ᴴ`。 -/
def app (ι : Type*) [Fintype ι] [DecidableEq ι] (Φ : Kraus κ r) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × κ) (ι × κ) ℂ :=
  sandwich fun a => (1 : Matrix ι ι ℂ) ⊗ₖ Φ.K a

theorem app_eq_idKron [DecidableEq ι] (Φ : Kraus κ r) : Φ.app ι = idKron Φ.toLin :=
  sandwich_one_kron Φ.K

/-- **T1 的 Kraus 版**：B 側的 Kraus 通道不改變 A 側的約化態。 -/
theorem no_signalling [DecidableEq ι] (Φ : Kraus κ r) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ptrB (Φ.app ι X) = ptrB X := by
  rw [app_eq_idKron]
  exact ptrB_idKron _ Φ.trace_toLin X

end Kraus

/-! ## 負控制：拿掉或改壞假設，結論必須失敗 -/

/-- **N1** 拿掉保跡：零映射配 Bell 態，A 側約化態改變。所以 `hTP` 不能刪。 -/
theorem negctrl_not_tp :
    ptrB (idKron (0 : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (maxEnt (Fin 2))) ≠ ptrB (maxEnt (Fin 2)) := by
  rw [ptrB_maxEnt]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num at h00

/-- unital 但不保跡的一組 Kraus 算子：`K₁ = |0⟩⟨0|`、`K₂ = |1⟩⟨0|`。 -/
def kUnital : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![single 0 0 1, single 1 0 1]

theorem kUnital_unital : ∑ a, kUnital a * (kUnital a)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kUnital, Fin.sum_univ_two, one_apply]

theorem kUnital_not_tp : ∑ a, (kUnital a)ᴴ * kUnital a ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [kUnital, Fin.sum_univ_two] at h00

/-- **N2** 把保跡誤寫成 unital：`kUnital` 滿足 `Σ K Kᴴ = 1`，但 Bell 態的 A 側約化態會變。
擋 `Kraus.tp` 寫成 `Σ K_a K_aᴴ = 1`。 -/
theorem negctrl_unital_not_tp :
    ptrB (sandwich (fun a => (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ kUnital a) (maxEnt (Fin 2))) ≠
      ptrB (maxEnt (Fin 2)) := by
  rw [sandwich_one_kron, ptrB_maxEnt]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [ptrB_idKron_apply, trace_sandwich] at h00
  simp [kUnital, maxEnt, trace, Fin.sum_univ_two, mul_apply, single_apply,
    vecMulVec_apply] at h00

/-- B 側的置換通道 `M ↦ tr M · |0⟩⟨0|`（保跡）。 -/
def replace0 : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun M := trace M • single 0 0 1
  map_add' M N := by simp [trace_add, add_smul]
  map_smul' c M := by simp [trace_smul]

theorem trace_replace0 (M : Matrix (Fin 2) (Fin 2) ℂ) : trace (replace0 M) = trace M := by
  simp [replace0, trace, Fin.sum_univ_two]

/-- **N3** 結論不是「所有邊際都不變」：B 側置換通道保住 A 側約化態（由 T1），
但 B 側約化態變了。 -/
theorem negctrl_replace_changes_ptrA :
    ptrB (idKron replace0 (maxEnt (Fin 2))) = ptrB (maxEnt (Fin 2)) ∧
      ptrA (idKron replace0 (maxEnt (Fin 2))) ≠ ptrA (maxEnt (Fin 2)) := by
  refine ⟨ptrB_idKron _ trace_replace0 _, ?_⟩
  rw [ptrA_maxEnt]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [replace0] at h11

/-- **N4** 局域性是必要的：改在 A 側施重置通道 `R(M) = tr M · |0⟩⟨0|`，
`(R ⊗ id) X = |0⟩⟨0| ⊗ Tr_A X`，A 側約化態就變了。 -/
theorem negctrl_A_side_changes_ptrB :
    ptrB (single (0 : Fin 2) 0 (1 : ℂ) ⊗ₖ ptrA (maxEnt (Fin 2))) ≠ ptrB (maxEnt (Fin 2)) := by
  rw [ptrB_kronecker, ptrB_maxEnt]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp at h11

/-! ## 見證：假設可以同時成立，定理不是空的 -/

/-- Pauli X。 -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli X 通道（單一 Kraus 算子）。 -/
def krausX : Kraus (Fin 2) (Fin 1) where
  K := fun _ => pauliX
  tp := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, mul_apply, Fin.sum_univ_two, conjTranspose_apply]

/-- amplitude damping，γ = 9/25：`K₀ = diag(1, 4/5)`、`K₁ = (3/5)|0⟩⟨1|`。保跡但不 unital。 -/
def ampK : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![!![1, 0; 0, 4/5], !![0, 3/5; 0, 0]]

def krausAmp : Kraus (Fin 2) (Fin 2) where
  K := ampK
  tp := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ampK, mul_apply, Fin.sum_univ_two, conjTranspose_apply, map_ofNat]
    norm_num

theorem ampK_not_unital : ∑ a, ampK a * (ampK a)ᴴ ≠ 1 := by
  intro h
  have h00 : (∑ a, ampK a * (ampK a)ᴴ) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  rw [Matrix.sum_apply, Fin.sum_univ_two, mul_apply, mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two] at h00
  simp [ampK, conjTranspose_apply] at h00

theorem witness_pauliX [DecidableEq ι] (X : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) :
    ptrB (krausX.app ι X) = ptrB X :=
  krausX.no_signalling X

theorem witness_amplitudeDamping [DecidableEq ι] (X : Matrix (ι × Fin 2) (ι × Fin 2) ℂ) :
    ptrB (krausAmp.app ι X) = ptrB X :=
  krausAmp.no_signalling X

/-- 轉置映射。 -/
def transposeMap : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun M := Mᵀ
  map_add' M N := transpose_add M N
  map_smul' c M := by simp

omit [Fintype ι] in
/-- 轉置保跡，所以 T1 適用。它不是完全正映射（`transposeMap_not_completelyPositive`），
所以 T1 談的是「保跡線性映射」，不是「物理通道」。 -/
theorem witness_transpose (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ptrB (idKron transposeMap X) = ptrB X :=
  ptrB_idKron _ (fun M => trace_transpose M) X

omit [Fintype κ] in
@[simp] theorem transposeMap_apply (M : Matrix κ κ ℂ) : transposeMap M = Mᵀ := rfl

/-- 反對稱向量 `|01⟩ - |10⟩`。 -/
def singletVec : Fin 2 × Fin 2 → ℂ := fun p =>
  if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- **轉置不是完全正**：Bell 態是半正定的，但 `id ⊗ T`（部分轉置）之後不是：
在 `|01⟩ - |10⟩` 上的期望值是 -1。這正是完全正性在 k = 2 時的失敗。 -/
theorem transposeMap_not_completelyPositive :
    (maxEnt (Fin 2)).PosSemidef ∧ ¬ (idKron transposeMap (maxEnt (Fin 2))).PosSemidef := by
  refine ⟨?_, fun h => ?_⟩
  · rw [maxEnt]
    refine (posSemidef_vecMulVec_self_star _).smul ?_
    rw [show ((Fintype.card (Fin 2) : ℂ))⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by simp]
    exact Complex.zero_le_real.mpr (by norm_num)
  · have hv := h.dotProduct_mulVec_nonneg singletVec
    simp [singletVec, maxEnt, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      vecMulVec_apply] at hv
    rw [Complex.le_def] at hv
    norm_num at hv

end

end ErEpr
