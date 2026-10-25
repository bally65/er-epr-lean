import ErEpr.Monogamy

/-!
# ErEpr.Swapping：糾纏交換——從沒交互過的兩端接上一條線

四個 qubit A、B、C、D（指標 `((a, b), (c, d))`）。起點是兩對 Bell 態 `Bell_AB ⊗ Bell_CD`
（`maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)`）：A 只和 B 糾纏，D 只和 C 糾纏，A 與 D 從沒交互過。

* **交換之前**（`swap_before`）：A–D 的約化態是 `½·1 ⊗ ½·1`，互資訊 0。
* **交換**（`entanglement_swapping`）：對中間的 B、C 做 Bell 投影 `Π = 1_A ⊗ |Φ⁺⟩⟨Φ⁺|_BC ⊗ 1_D`
  （`swapProj 0 0`）。這個結果的機率是 `1/4`，歸一化之後 A–D 的約化態**恰好是 Bell 態**，
  互資訊從 0 變成 `2 ln 2`。核心只有一行：`Σ_{b,c} [b = c]·[a = b][c = d] = [a = d]`
  （`swapProj_mulVec`）。
* **四個結果平均，A–D 什麼都沒變**（`swap_average_no_signalling`）：B、C 的四個 Bell 結果
  `β_st`（`swapProj s t`）各自機率 `1/4`（`swap_prob`），各自把 A–D 接成一個 Bell 態；但不知道
  是哪一個結果時，四者平均起來 A–D 的約化態**與交換前完全相同**。要知道「接上了」，
  得有人用古典通道告訴 D 結果是哪一個：交換能接上糾纏，但不能傳訊息。
* **負控制：相交點必須是糾纏的測量**（`negctrl_swap_separate`）：B、C 改成各自量到 `|0⟩`
  （`sepProj`，不糾纏的測量），歸一化之後 A–D 是乘積態 `|0⟩⟨0| ⊗ |0⟩⟨0|`，互資訊仍是 0。
* 記帳：`ptrBC` 一次跡掉中間的 B、C；保真 `ptrBC_kronecker`（`Tr_BC(X_AB ⊗ Y_CD) = Tr_B X ⊗ Tr_C Y`）、
  `trace_ptrBC`。

物理讀法：兩端不必直接碰過面，但中間要有一條「相交點」串起來的鏈（這裡是 B、C 的聯合測量）。
在 ER=EPR 的圖像裡，這相當於把兩條蟲洞接成一條（Susskind 等的說法）；本庫沒有幾何的模型，
這段只是說明文字。

範圍（引用前請讀）：
* 四個 qubit、一次 Bell 測量；測量寫成「投影＋事後挑選」，沒有一般的量子儀器形式化。
* 「各自量」的負控制只有 `|0⟩|0⟩` 這一個結果；沒有證「任何局部操作加古典通訊（LOCC）
  都造不出糾纏」這個一般定理。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder Real

noncomputable section

/-! ## 互資訊與跡掉中間兩個 -/

/-- 互資訊 `I(A:B) = S(A) + S(B) − S(AB)`。 -/
def mutualInfo {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix (ι × κ) (ι × κ) ℂ) : ℝ :=
  vnEntropy (ptrB X) + vnEntropy (ptrA X) - vnEntropy X

/-- 乘積態的互資訊是 0。 -/
theorem mutualInfo_kronecker {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : trace A = 1) (htB : trace B = 1) : mutualInfo (A ⊗ₖ B) = 0 := by
  rw [mutualInfo, ptrB_kronecker, ptrA_kronecker, htA, htB, one_smul, one_smul,
    vnEntropy_kronecker hA hB htA htB]
  ring

/-- 四方態 `((a, b), (c, d))` 跡掉中間的 B、C，得到 A–D 的約化態。 -/
def ptrBC {ια ιβ ιγ ιδ : Type*} [Fintype ιβ] [Fintype ιγ]
    (X : Matrix ((ια × ιβ) × (ιγ × ιδ)) ((ια × ιβ) × (ιγ × ιδ)) ℂ) : Matrix (ια × ιδ) (ια × ιδ) ℂ :=
  Matrix.of fun p q => ∑ b, ∑ c, X ((p.1, b), (c, p.2)) ((q.1, b), (c, q.2))

/-- 保真：`Tr_BC(X_AB ⊗ Y_CD) = Tr_B X ⊗ Tr_C Y`。 -/
theorem ptrBC_kronecker {ια ιβ ιγ ιδ : Type*} [Fintype ιβ] [Fintype ιγ]
    (X : Matrix (ια × ιβ) (ια × ιβ) ℂ) (Y : Matrix (ιγ × ιδ) (ιγ × ιδ) ℂ) :
    ptrBC (X ⊗ₖ Y) = ptrB X ⊗ₖ ptrA Y := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [ptrBC, Matrix.of_apply, kroneckerMap_apply, ptrB_apply, ptrA_apply, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem ptrBC_smul {ια ιβ ιγ ιδ : Type*} [Fintype ιβ] [Fintype ιγ] (r : ℂ)
    (X : Matrix ((ια × ιβ) × (ιγ × ιδ)) ((ια × ιβ) × (ιγ × ιδ)) ℂ) :
    ptrBC (r • X) = r • ptrBC X := by
  ext p q
  simp only [ptrBC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- 保跡。 -/
theorem trace_ptrBC {ια ιβ ιγ ιδ : Type*} [Fintype ια] [Fintype ιβ] [Fintype ιγ] [Fintype ιδ]
    (X : Matrix ((ια × ιβ) × (ιγ × ιδ)) ((ια × ιβ) × (ιγ × ιδ)) ℂ) :
    trace (ptrBC X) = trace X := by
  simp only [trace, diag_apply, ptrBC, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- `|v⟩⟨w| ⊗ |x⟩⟨y| = |v ⊗ x⟩⟨w ⊗ y|`。 -/
theorem vecMulVec_kronecker {ι κ ι' κ' : Type*} (v : ι → ℂ) (w : κ → ℂ) (x : ι' → ℂ) (y : κ' → ℂ) :
    vecMulVec v w ⊗ₖ vecMulVec x y =
      vecMulVec (fun p : ι × ι' => v p.1 * x p.2) (fun q : κ × κ' => w q.1 * y q.2) := by
  ext ⟨i, i'⟩ ⟨k, k'⟩
  simp only [kroneckerMap_apply, vecMulVec_apply]
  ring

/-! ## 起點與 Bell 投影 -/

/-- 四個 qubit 的指標 `((a, b), (c, d))`。 -/
abbrev Q4 := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- 兩對 Bell 態的（未歸一化）向量 `[a = b]·[c = d]`。 -/
def bellPairVec : Q4 → ℂ := fun p => vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ) p.1 *
  vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ) p.2

/-- `Bell_AB ⊗ Bell_CD = (1/4)·|ψ⟩⟨ψ|`。 -/
theorem bellPair_eq :
    maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2) = (1 / 4 : ℂ) • vecMulVec bellPairVec (star bellPairVec) := by
  rw [maxEnt, smul_kronecker, kronecker_smul, smul_smul, vecMulVec_kronecker]
  congr 1
  · norm_num
  · congr 1
    funext q
    simp only [bellPairVec, Pi.star_apply, star_mul']

/-- `Fin 2` 的加法：`1 + 1 = 0`（逐格計算用）。 -/
@[simp] theorem fin_two_one_add_one : (1 : Fin 2) + 1 = 0 := by decide

/-- 符號 `(−1)^{s·x}`。 -/
def bellSign (s x : Fin 2) : ℂ := if s = 1 ∧ x = 1 then -1 else 1

/-- B、C 上的 Bell 投影 `|β_st⟩⟨β_st|`（`β_st(b, c) = [c = b + t]·(−1)^{s·b}/√2`），A、D 不動。
`s = t = 0` 是 `Φ⁺`。 -/
def swapProj (s t : Fin 2) : Matrix Q4 Q4 ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 ∧ p.2.1 = p.1.2 + t ∧ q.2.1 = q.1.2 + t then
      (1 / 2 : ℂ) * bellSign s p.1.2 * bellSign s q.1.2
    else 0

/-- 投影之後的（未歸一化）向量：`(1/2)·[c = b + t]·[d = a + t]·(−1)^{s(a+b)}`。 -/
def swapVec (s t : Fin 2) : Q4 → ℂ := fun p =>
  (1 / 2 : ℂ) * (if p.2.1 = p.1.2 + t ∧ p.2.2 = p.1.1 + t then 1 else 0) *
    bellSign s p.1.1 * bellSign s p.1.2

/-- **核心一行**：`Π_st ψ = swapVec s t`；`s = t = 0` 時就是 `Σ_{b,c}[b = c][a = b][c = d] = [a = d]`。 -/
theorem swapProj_mulVec (s t : Fin 2) : swapProj s t *ᵥ bellPairVec = swapVec s t := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  fin_cases s <;> fin_cases t <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [swapProj, bellPairVec, swapVec, bellSign, mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

theorem vecMul_swapProj (s t : Fin 2) : star bellPairVec ᵥ* swapProj s t = star (swapVec s t) := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  fin_cases s <;> fin_cases t <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [swapProj, bellPairVec, swapVec, bellSign, vecMul, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

/-- 投影之後：`Π ρ Π = (1/4)·|swapVec⟩⟨swapVec|`。 -/
theorem swap_post (s t : Fin 2) :
    swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t =
      (1 / 4 : ℂ) • vecMulVec (swapVec s t) (star (swapVec s t)) := by
  rw [bellPair_eq, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, swapProj_mulVec,
    vecMul_swapProj]

/-- A–D 那一側的 Bell 態 `β_st`（`(1/2)·[d = a + t][d' = a' + t]·(−1)^{s(a+a')}`）。 -/
def bellAD (s t : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    (1 / 2 : ℂ) * (if p.2 = p.1 + t ∧ q.2 = q.1 + t then 1 else 0) * bellSign s p.1 * bellSign s q.1

/-- `swapVec` 是實數向量：`star` 不改變它。 -/
theorem star_swapVec (s t : Fin 2) : star (swapVec s t) = swapVec s t := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  fin_cases s <;> fin_cases t <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [swapVec, bellSign]

theorem ptrBC_swapVec_00 : ptrBC (vecMulVec (swapVec 0 0) (swapVec 0 0)) = bellAD 0 0 := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ptrBC, swapVec, bellAD, bellSign, vecMulVec_apply, Fin.sum_univ_two]

theorem ptrBC_swapVec_01 : ptrBC (vecMulVec (swapVec 0 1) (swapVec 0 1)) = bellAD 0 1 := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ptrBC, swapVec, bellAD, bellSign, vecMulVec_apply, Fin.sum_univ_two]

theorem ptrBC_swapVec_10 : ptrBC (vecMulVec (swapVec 1 0) (swapVec 1 0)) = bellAD 1 0 := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ptrBC, swapVec, bellAD, bellSign, vecMulVec_apply, Fin.sum_univ_two]

theorem ptrBC_swapVec_11 : ptrBC (vecMulVec (swapVec 1 1) (swapVec 1 1)) = bellAD 1 1 := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ptrBC, swapVec, bellAD, bellSign, vecMulVec_apply, Fin.sum_univ_two]

theorem ptrBC_swapVec (s t : Fin 2) :
    ptrBC (vecMulVec (swapVec s t) (star (swapVec s t))) = bellAD s t := by
  rw [star_swapVec]
  fin_cases s <;> fin_cases t
  · exact ptrBC_swapVec_00
  · exact ptrBC_swapVec_01
  · exact ptrBC_swapVec_10
  · exact ptrBC_swapVec_11

theorem trace_bellAD (s t : Fin 2) : trace (bellAD s t) = 1 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [trace, bellAD, bellSign, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bellAD_zero : bellAD 0 0 = maxEnt (Fin 2) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [bellAD, bellSign, maxEnt, vecMulVec_apply, Matrix.one_apply]

/-- A–D 的約化態：每個結果都是 `(1/4)·β_st`。 -/
theorem ptrBC_swap_post (s t : Fin 2) :
    ptrBC (swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t) =
      (1 / 4 : ℂ) • bellAD s t := by
  rw [swap_post, ptrBC_smul, ptrBC_swapVec]

/-- 每個 Bell 結果的機率都是 `1/4`。 -/
theorem swap_prob (s t : Fin 2) :
    trace (swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t) = 1 / 4 := by
  rw [← trace_ptrBC, ptrBC_swap_post, trace_smul, trace_bellAD, smul_eq_mul, mul_one]

/-! ## 交換之前與之後 -/

/-- **交換之前**：A–D 是乘積態 `½·1 ⊗ ½·1`，互資訊 0。 -/
theorem swap_before :
    ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) = mix2 ⊗ₖ mix2 ∧
      mutualInfo (ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2))) = 0 := by
  have h : ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) = mix2 ⊗ₖ mix2 := by
    rw [ptrBC_kronecker, ptrB_bell_eq_mix2, ptrA_maxEnt, ← ptrB_maxEnt, ptrB_bell_eq_mix2]
  refine ⟨h, ?_⟩
  rw [h]
  exact mutualInfo_kronecker mix2_posSemidef.1 mix2_posSemidef.1 trace_mix2 trace_mix2

/-- **糾纏交換**：對 B、C 做 Bell 投影 `Φ⁺`，機率 `1/4`；歸一化之後 A–D 的約化態恰好是 Bell 態，
互資訊從 0 變成 `2 ln 2`。 -/
theorem entanglement_swapping :
    trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) = 1 / 4 ∧
      (trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0))⁻¹ •
          ptrBC (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) =
        maxEnt (Fin 2) ∧
      mutualInfo (ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2))) = 0 ∧
      mutualInfo ((trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0))⁻¹ •
          ptrBC (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0)) =
        2 * Real.log 2 := by
  have hpost : (trace (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0))⁻¹ •
      ptrBC (swapProj 0 0 * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj 0 0) = maxEnt (Fin 2) := by
    rw [swap_prob, ptrBC_swap_post, smul_smul, bellAD_zero]
    norm_num
  refine ⟨swap_prob 0 0, hpost, swap_before.2, ?_⟩
  rw [hpost, mutualInfo]
  exact bell_mutual_information

/-! ## 四個結果平均：不能傳訊息 -/

/-- 四個結果的 A–D 約化態加總（各帶機率 `1/4`）正好是 `½·1 ⊗ ½·1`。 -/
theorem swap_average_eq :
    ∑ s : Fin 2, ∑ t : Fin 2,
        ptrBC (swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t) =
      mix2 ⊗ₖ mix2 := by
  simp only [ptrBC_swap_post]
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [Matrix.sum_apply, bellAD, bellSign, mix2, kroneckerMap_apply, Fin.sum_univ_two]

/-- **不能傳訊息**：不知道 B、C 量到哪一個結果時，四個結果平均起來，A–D 的約化態與交換前完全相同。 -/
theorem swap_average_no_signalling :
    ∑ s : Fin 2, ∑ t : Fin 2,
        ptrBC (swapProj s t * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * swapProj s t) =
      ptrBC (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) := by
  rw [swap_average_eq, swap_before.1]

/-! ## 負控制：相交點必須是糾纏的測量 -/

/-- B、C 各自量到 `|0⟩`（不糾纏的測量）：`1_A ⊗ |0⟩⟨0|_B ⊗ |0⟩⟨0|_C ⊗ 1_D`。 -/
def sepProj : Matrix Q4 Q4 ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 ∧ p.2.2 = q.2.2 ∧ p.1.2 = 0 ∧ p.2.1 = 0 ∧ q.1.2 = 0 ∧ q.2.1 = 0 then 1 else 0

/-- 各自量之後的向量 `|0000⟩`。 -/
def sepVec : Q4 → ℂ := fun p => if p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2.1 = 0 ∧ p.2.2 = 0 then 1 else 0

theorem sepProj_mulVec : sepProj *ᵥ bellPairVec = sepVec := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sepProj, bellPairVec, sepVec, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]

theorem vecMul_sepProj : star bellPairVec ᵥ* sepProj = star sepVec := by
  funext p
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sepProj, bellPairVec, sepVec, vecMul, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.one_apply]

theorem ptrBC_sepVec : ptrBC (vecMulVec sepVec (star sepVec)) = ket0Proj ⊗ₖ ket0Proj := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    norm_num [ptrBC, sepVec, ket0Proj, vecMulVec_apply, kroneckerMap_apply, Fin.sum_univ_two]

/-- **負控制**：B、C 各自量到 `|0⟩`，機率 `1/4`；歸一化之後 A–D 是乘積態，互資訊仍是 0。 -/
theorem negctrl_swap_separate :
    trace (sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj) = 1 / 4 ∧
      mutualInfo ((trace (sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj))⁻¹ •
        ptrBC (sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj)) = 0 := by
  have hpost : sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj =
      (1 / 4 : ℂ) • vecMulVec sepVec (star sepVec) := by
    rw [bellPair_eq, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, sepProj_mulVec,
      vecMul_sepProj]
  have hAD : ptrBC (sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj) =
      (1 / 4 : ℂ) • (ket0Proj ⊗ₖ ket0Proj) := by
    rw [hpost, ptrBC_smul, ptrBC_sepVec]
  have htr : trace (sepProj * (maxEnt (Fin 2) ⊗ₖ maxEnt (Fin 2)) * sepProj) = 1 / 4 := by
    rw [← trace_ptrBC, hAD, trace_smul, trace_kronecker, trace_ket0Proj, smul_eq_mul]
    norm_num
  refine ⟨htr, ?_⟩
  rw [htr, hAD, smul_smul]
  norm_num
  exact mutualInfo_kronecker ket0Proj_posSemidef.1 ket0Proj_posSemidef.1 trace_ket0Proj trace_ket0Proj

/-! ## Π 是完整的投影測量

`swapProj s t` 換個指標順序 `((a, b), (c, d)) ↦ ((a, d), (b, c))`，就是 `1_AD ⊗ |β_st⟩⟨β_st|_BC`
（`swapProj_eq_reindex`）。所以它是 Hermitian 投影（`swapProj_isHermitian`、`swapProj_mul_self`），
而且四個加起來是單位矩陣（`sum_swapProj`）：「四個結果」是一個完整的測量。 -/

theorem star_bellSign (s x : Fin 2) : star (bellSign s x) = bellSign s x := by
  unfold bellSign
  split_ifs <;> simp

/-- B、C 上的（未歸一化）Bell 向量 `β_st(b, c) = [c = b + t]·(−1)^{s·b}`。 -/
def bellVecBC (s t : Fin 2) : Fin 2 × Fin 2 → ℂ := fun x => if x.2 = x.1 + t then bellSign s x.1 else 0

/-- B、C 上的 Bell 投影 `(1/2)·|β_st⟩⟨β_st|`。 -/
def bellProjBC (s t : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • vecMulVec (bellVecBC s t) (star (bellVecBC s t))

theorem bellVecBC_norm (s t : Fin 2) :
    (1 / 2 : ℂ) * ∑ i, star (bellVecBC s t i) * bellVecBC s t i = 1 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [bellVecBC, bellSign, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bellProjBC_mul_self (s t : Fin 2) : bellProjBC s t * bellProjBC s t = bellProjBC s t :=
  rankOne_mul_self (bellVecBC_norm s t)

theorem bellProjBC_conjTranspose (s t : Fin 2) : (bellProjBC s t)ᴴ = bellProjBC s t :=
  rankOne_conjTranspose (by simp) _

theorem sum_bellProjBC : ∑ s : Fin 2, ∑ t : Fin 2, bellProjBC s t = 1 := by
  ext ⟨b, c⟩ ⟨b', c'⟩
  fin_cases b <;> fin_cases c <;> fin_cases b' <;> fin_cases c' <;>
    norm_num [Matrix.sum_apply, bellProjBC, bellVecBC, bellSign, vecMulVec_apply, Fin.sum_univ_two,
      Matrix.one_apply]

/-- 指標重排 `((a, b), (c, d)) ↦ ((a, d), (b, c))`：把 B、C 放到一起。 -/
def swapReindex : Q4 ≃ (Fin 2 × Fin 2) × (Fin 2 × Fin 2) where
  toFun p := ((p.1.1, p.2.2), (p.1.2, p.2.1))
  invFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Π 的結構**：`swapProj s t` 就是重排過的 `1_AD ⊗ |β_st⟩⟨β_st|_BC`。 -/
theorem swapProj_eq_reindex (s t : Fin 2) :
    swapProj s t =
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ bellProjBC s t).submatrix swapReindex
        swapReindex := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  simp only [swapProj, Matrix.of_apply, submatrix_apply, swapReindex, Equiv.coe_fn_mk,
    kroneckerMap_apply, bellProjBC, Matrix.smul_apply, vecMulVec_apply, bellVecBC, Pi.star_apply,
    smul_eq_mul, one_apply, Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : d = d' <;> by_cases h3 : c = b + t <;>
    by_cases h4 : c' = b' + t <;> simp [h1, h2, h3, h4, star_bellSign, mul_assoc]

/-- **Π 是 Hermitian**。 -/
theorem swapProj_isHermitian (s t : Fin 2) : (swapProj s t).IsHermitian := by
  rw [Matrix.IsHermitian, swapProj_eq_reindex, conjTranspose_submatrix, conjTranspose_kronecker,
    conjTranspose_one, bellProjBC_conjTranspose]

/-- **Π² = Π**：`swapProj s t` 是投影。 -/
theorem swapProj_mul_self (s t : Fin 2) : swapProj s t * swapProj s t = swapProj s t := by
  rw [swapProj_eq_reindex, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul,
    bellProjBC_mul_self]

/-- **完備性**：四個 Bell 投影加起來是單位矩陣。 -/
theorem sum_swapProj : ∑ s : Fin 2, ∑ t : Fin 2, swapProj s t = 1 := by
  have h : ∑ s : Fin 2, ∑ t : Fin 2, swapProj s t =
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ⊗ₖ ∑ s : Fin 2, ∑ t : Fin 2, bellProjBC s t).submatrix
        swapReindex swapReindex := by
    simp only [swapProj_eq_reindex]
    ext p q
    simp only [Matrix.sum_apply, submatrix_apply, kroneckerMap_apply, Finset.mul_sum]
  rw [h, sum_bellProjBC, one_kronecker_one, submatrix_one_equiv]

/-! ## AMPS 防火牆矛盾：一夫一妻的直接推論 -/

/-- 三方態 `((a, b), r)` 跡掉第一個（A），得到 B–R 的約化態。 -/
def ptrFirst {ια ιβ ιρ : Type*} [Fintype ια]
    (X : Matrix ((ια × ιβ) × ιρ) ((ια × ιβ) × ιρ) ℂ) : Matrix (ιβ × ιρ) (ιβ × ιρ) ℂ :=
  Matrix.of fun p q => ∑ a, X ((a, p.1), p.2) ((a, q.1), q.2)

theorem ptrFirst_kronecker {ια ιβ ιρ : Type*} [Fintype ια]
    (Y : Matrix (ια × ιβ) (ια × ιβ) ℂ) (Z : Matrix ιρ ιρ ℂ) :
    ptrFirst (Y ⊗ₖ Z) = ptrA Y ⊗ₖ Z := by
  ext ⟨b, r⟩ ⟨b', r'⟩
  simp only [ptrFirst, Matrix.of_apply, kroneckerMap_apply, ptrA_apply, Finset.sum_mul]

/-- 保真：`Tr_A((A ⊗ B) ⊗ C) = (tr A)·(B ⊗ C)`，跡掉的確實是第一個。 -/
theorem ptrFirst_kronecker3 {ια ιβ ιρ : Type*} [Fintype ια] (A : Matrix ια ια ℂ)
    (B : Matrix ιβ ιβ ℂ) (C : Matrix ιρ ιρ ℂ) :
    ptrFirst ((A ⊗ₖ B) ⊗ₖ C) = trace A • (B ⊗ₖ C) := by
  rw [ptrFirst_kronecker, ptrA_kronecker, smul_kronecker]

/-- **AMPS 的核心（一般版）**：A–B 的聯合態是純態 `c·|v⟩⟨v|` 時，B 與 R 的約化態是乘積態，
互資訊 `I(B:R) = 0`。 -/
theorem amps_monogamy {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] {ρ : Matrix ((ι × κ) × μ) ((ι × κ) × μ) ℂ} (hρ : ρ.PosSemidef)
    {c : ℂ} {v : ι × κ → ℂ} (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1)
    (hpure : ptrB ρ = c • vecMulVec v (star v)) :
    ptrFirst ρ = ptrA (ptrB ρ) ⊗ₖ ptrA ρ ∧ mutualInfo (ptrFirst ρ) = 0 := by
  have hm := monogamy hρ hcs hc hpure
  have hBR : ptrFirst ρ = ptrA (ptrB ρ) ⊗ₖ ptrA ρ := by
    conv_lhs => rw [hm]
    rw [ptrFirst_kronecker]
  refine ⟨hBR, ?_⟩
  have hAB := ptrB_posSemidef hρ
  have htrAB : trace (ptrB ρ) = 1 := by rw [hpure, trace_rankOne hc]
  have hB := ptrA_posSemidef hAB
  have htrB : trace (ptrA (ptrB ρ)) = 1 := by rw [trace_ptrA, htrAB]
  have hR := ptrA_posSemidef hρ
  have htrR : trace (ptrA ρ) = 1 := by rw [trace_ptrA, ← trace_ptrB, htrAB]
  rw [hBR]
  exact mutualInfo_kronecker hB.1 hR.1 htrB htrR

/-- **AMPS 矛盾**：沒有任何三方態能同時讓 A–B 是 Bell 態（視界平滑）又讓 B–R 的互資訊是
`2 ln 2`（B 與早期輻射最大相關）。 -/
theorem amps_contradiction {μ : Type*} [Fintype μ] [DecidableEq μ] :
    ¬ ∃ ρ : Matrix ((Fin 2 × Fin 2) × μ) ((Fin 2 × Fin 2) × μ) ℂ, ρ.PosSemidef ∧
      ptrB ρ = maxEnt (Fin 2) ∧ mutualInfo (ptrFirst ρ) = 2 * Real.log 2 := by
  rintro ⟨ρ, hρ, hbell, hI⟩
  have hcs : star ((Fintype.card (Fin 2) : ℂ))⁻¹ = ((Fintype.card (Fin 2) : ℂ))⁻¹ := by simp
  have hpure : ptrB ρ = ((Fintype.card (Fin 2) : ℂ))⁻¹ •
      vecMulVec (vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ)) (star (vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [hbell]
    rfl
  rw [(amps_monogamy hρ hcs bell_rankOne_norm hpure).2] at hI
  linarith [Real.log_pos one_lt_two]

/-- 只要求 B 與早期輻射 R 最大相關的態：`½·1_A ⊗ Bell_BR`（重排成 `((a, b), r)`）。 -/
def ampsUnitaryState : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (mix2 ⊗ₖ maxEnt (Fin 2)).submatrix (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2))
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2))

theorem ampsUnitaryState_posSemidef : ampsUnitaryState.PosSemidef :=
  (mix2_posSemidef.kronecker maxEnt_posSemidef).submatrix _

theorem ptrFirst_ampsUnitaryState : ptrFirst ampsUnitaryState = maxEnt (Fin 2) := by
  ext ⟨b, r⟩ ⟨b', r'⟩
  simp only [ptrFirst, ampsUnitaryState, Matrix.of_apply, submatrix_apply, Equiv.prodAssoc_apply,
    kroneckerMap_apply]
  rw [← Finset.sum_mul]
  have h : ∑ a : Fin 2, mix2 a a = 1 := trace_mix2
  rw [h, one_mul]

/-- **兩個要求各自都能滿足**：只要 A–B 是 Bell（`Bell_AB ⊗ |0⟩⟨0|_R`），或只要 B–R 的互資訊是
`2 ln 2`（`ampsUnitaryState`）。矛盾來自兩者同時成立，不是任何一個本身不可能。 -/
theorem amps_each_half_satisfiable :
    ((maxEnt (Fin 2) ⊗ₖ ket0Proj).PosSemidef ∧
        ptrB (maxEnt (Fin 2) ⊗ₖ ket0Proj) = maxEnt (Fin 2)) ∧
      (ampsUnitaryState.PosSemidef ∧ mutualInfo (ptrFirst ampsUnitaryState) = 2 * Real.log 2) := by
  refine ⟨bell_monogamy_witness, ampsUnitaryState_posSemidef, ?_⟩
  rw [ptrFirst_ampsUnitaryState, mutualInfo]
  exact bell_mutual_information

/-! ### 負控制：A–B 只是古典相關時，B 可以同時和 R 有相關（GHZ） -/

/-- GHZ 態的（未歸一化）向量 `[a = b = r]`。 -/
def ghzVec : (Fin 2 × Fin 2) × Fin 2 → ℂ := fun p => if p.1.1 = p.1.2 ∧ p.1.2 = p.2 then 1 else 0

/-- GHZ 態 `(|000⟩ + |111⟩)/√2` 的密度矩陣 `(1/2)·|v⟩⟨v|`。 -/
def ghzState : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • vecMulVec ghzVec (star ghzVec)

theorem ghzState_posSemidef : ghzState.PosSemidef :=
  (posSemidef_vecMulVec_self_star ghzVec).smul (Complex.zero_le_real.mpr (by norm_num))

/-- GHZ 的 B–R 約化態 `diag(½, 0, 0, ½)`。 -/
theorem ptrFirst_ghzState :
    ptrFirst ghzState = diagonal fun p : Fin 2 × Fin 2 => ((if p.1 = p.2 then 1 / 2 else 0 : ℝ) : ℂ) := by
  ext ⟨b, r⟩ ⟨b', r'⟩
  fin_cases b <;> fin_cases r <;> fin_cases b' <;> fin_cases r' <;>
    norm_num [ptrFirst, ghzState, ghzVec, vecMulVec_apply, Fin.sum_univ_two]

theorem ptrB_ptrFirst_ghzState : ptrB (ptrFirst ghzState) = mix2 := by
  rw [ptrFirst_ghzState]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mix2, Fin.sum_univ_two]

theorem ptrA_ptrFirst_ghzState : ptrA (ptrFirst ghzState) = mix2 := by
  rw [ptrFirst_ghzState]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mix2, Fin.sum_univ_two]

theorem mutualInfo_ptrFirst_ghzState : mutualInfo (ptrFirst ghzState) = Real.log 2 := by
  rw [mutualInfo, ptrB_ptrFirst_ghzState, ptrA_ptrFirst_ghzState, vnEntropy_mix2, ptrFirst_ghzState,
    vnEntropy_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Real.negMulLog]
  ring

/-- **負控制**：「A–B 是純態」拿不掉。GHZ 的 A–B 約化態不是 Bell 態（只是古典相關），
而 B 與 R 的互資訊是 `ln 2 > 0`。 -/
theorem negctrl_amps_mixed :
    ghzState.PosSemidef ∧ ptrB ghzState ≠ maxEnt (Fin 2) ∧ 0 < mutualInfo (ptrFirst ghzState) := by
  refine ⟨ghzState_posSemidef, fun h => ?_, ?_⟩
  · have h1 := congrFun (congrFun h (0, 0)) (1, 1)
    norm_num [ghzState, ghzVec, maxEnt, vecMulVec_apply, Fin.sum_univ_two, Matrix.one_apply] at h1
  · rw [mutualInfo_ptrFirst_ghzState]
    exact Real.log_pos one_lt_two

end

end ErEpr
