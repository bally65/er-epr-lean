import ErEpr.Correlated

/-!
# ErEpr.Monogamy：糾纏的一夫一妻

三方態 `ρ_ABC`（指標 `ν × μ`，`ν` 是 AB、`μ` 是 C）若 AB 的邊際是純態
`P = c·|v⟩⟨v|`（`c·⟨v, v⟩ = 1`），則整體必為 `P ⊗ ρ_C`（`monogamy`）。

* 證法（不用固有值連續性，也不用 C*-代數）：
  1. `R = (1 − P) ⊗ 1` 是投影；由部分跡的對偶刻畫，`tr(ρR) = tr(P(1 − P)) = 0`；
  2. **半正定那一步**（`mul_eq_zero_of_trace_mul_eq_zero`）：`ρ = BᴴB`（`B = √D·Uᴴ`，
     `exists_eq_conjTranspose_mul_self`），`tr(ρR) = tr((BR)(BR)ᴴ) = 0 ⇒ BR = 0 ⇒ ρR = 0`；
  3. `(P ⊗ 1) + R = 1`，所以 `ρ = (P ⊗ 1)ρ(P ⊗ 1)`；
  4. 區塊計算（`rankOne_kron_one_conj`）：`(P ⊗ 1)ρ(P ⊗ 1) = P ⊗ X`，再跡掉 AB 得 `X = ρ_C`。
* **A 與 C 不相關**（`monogamy_mutualInfo`）：AB = A × B 時，跡掉中間的 B（`ptrMid`，
  保真 `ptrMid_kronecker3`）得 `ρ_AC = ρ_A ⊗ ρ_C`，互資訊 `S(A) + S(C) − S(AC) = 0`。
* **Bell 實例**（`bell_monogamy`）：AB 的邊際是 Bell 態時，`ρ_ABC = Bell ⊗ ρ_C`，
  A 與 B 的互資訊是 `2 ln 2`（最大），A 與 C 是 0。假設可以滿足（`bell_monogamy_witness`）。
* **負控制**（`negctrl_monogamy_mixed`）：「AB」的邊際不是純態時結論失敗。把 Bell 態看成
  「一個 qubit（當 AB）加 C」：它的邊際是混合態，而整體不是乘積（`S = 0 ≠ 2 ln 2`）。

物理讀法：糾纏不能隨便共享；A 與 B 糾纏到純態，就沒有任何相關能分給 C。黑洞「防火牆悖論」
（Almheiri、Marolf、Polchinski、Sully 2012）用的就是一夫一妻性，ER=EPR 是為了解那個矛盾
提出的。本庫沒有黑洞內部或輻射的模型，這段只是說明文字。

範圍（引用前請讀）：
* 只證「邊際是純態 ⇒ 與第三方完全不相關」這個精確版本；量化的一夫一妻
  （CKW 不等式、squashed entanglement）沒有做。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder Real

noncomputable section

variable {ν μ : Type*} [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ]

/-! ## 半正定那一步 -/

/-- 半正定矩陣寫成 `BᴴB`：`B = √D·Uᴴ`（`ρ = U·D·Uᴴ`）。 -/
theorem exists_eq_conjTranspose_mul_self {ρ : Matrix ν ν ℂ} (hρ : ρ.PosSemidef) :
    ∃ B : Matrix ν ν ℂ, ρ = Bᴴ * B := by
  refine ⟨diagonal (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ)) * star (eigU hρ.1), ?_⟩
  have hd : star (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ) := by
    funext i
    simp
  have hsq : (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ) *
      ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ)) = fun i => (hρ.1.eigenvalues i : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg i)]
  rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
    hd, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal, hsq,
    ← Matrix.mul_assoc, ← star_eq_conjTranspose]
  exact eigU_spectral hρ.1

/-- **半正定那一步**：`ρ ≥ 0`、`R` 是 Hermitian 投影、`tr(ρR) = 0` ⇒ `ρR = 0`。 -/
theorem mul_eq_zero_of_trace_mul_eq_zero {ρ R : Matrix ν ν ℂ} (hρ : ρ.PosSemidef) (hRh : Rᴴ = R)
    (hR2 : R * R = R) (htr : trace (ρ * R) = 0) : ρ * R = 0 := by
  obtain ⟨B, rfl⟩ := exists_eq_conjTranspose_mul_self hρ
  have hBR : (B * R) * (B * R)ᴴ = B * R * Bᴴ := by
    rw [conjTranspose_mul, hRh, Matrix.mul_assoc B R, ← Matrix.mul_assoc R R, hR2, Matrix.mul_assoc]
  have h2 : trace ((B * R) * (B * R)ᴴ) = 0 := by
    rw [hBR, trace_mul_comm, ← Matrix.mul_assoc]
    exact htr
  rw [Matrix.mul_assoc, trace_mul_conjTranspose_self_eq_zero_iff.mp h2, Matrix.mul_zero]

/-! ## 秩一投影 -/

omit [DecidableEq ν] in
theorem rankOne_mul_self {c : ℂ} {v : ν → ℂ} (hc : c * ∑ i, star (v i) * v i = 1) :
    (c • vecMulVec v (star v)) * (c • vecMulVec v (star v)) = c • vecMulVec v (star v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  have h : ∑ k, c * (v i * star (v k)) * (c * (v k * star (v j))) =
      c * (v i * star (v j)) * (c * ∑ k, star (v k) * v k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h, hc, mul_one]

omit [Fintype ν] [DecidableEq ν] in
theorem rankOne_conjTranspose {c : ℂ} (hcs : star c = c) (v : ν → ℂ) :
    (c • vecMulVec v (star v))ᴴ = c • vecMulVec v (star v) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply,
    star_mul', star_star, hcs]
  ring

omit [DecidableEq ν] in
theorem trace_rankOne {c : ℂ} {v : ν → ℂ} (hc : c * ∑ i, star (v i) * v i = 1) :
    trace (c • vecMulVec v (star v)) = 1 := by
  rw [trace_smul, smul_eq_mul, ← hc]
  congr 1
  simp only [trace, diag_apply, vecMulVec_apply, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ν] in
/-- 區塊計算：`(|v⟩⟨w| ⊗ 1)ρ(|v⟩⟨w| ⊗ 1) = |v⟩⟨w| ⊗ X`，`X_ab = Σ w_n ρ_{(n,a),(n',b)} v_{n'}`。 -/
theorem rankOne_kron_one_conj (v w : ν → ℂ) (ρ : Matrix (ν × μ) (ν × μ) ℂ) :
    (vecMulVec v w ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ * (vecMulVec v w ⊗ₖ (1 : Matrix μ μ ℂ)) =
      vecMulVec v w ⊗ₖ (Matrix.of fun a b => ∑ n, ∑ n', w n * ρ (n, a) (n', b) * v n') := by
  ext ⟨m, a⟩ ⟨m', b⟩
  simp only [Matrix.mul_apply, kroneckerMap_apply, vecMulVec_apply, one_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.of_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => by ring

/-! ## 一夫一妻 -/

/-- **一夫一妻**：AB 的邊際是純態 `c·|v⟩⟨v|` 時，`ρ_ABC = ρ_AB ⊗ ρ_C`。 -/
theorem monogamy {ρ : Matrix (ν × μ) (ν × μ) ℂ} (hρ : ρ.PosSemidef) {c : ℂ} {v : ν → ℂ}
    (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1)
    (hpure : ptrB ρ = c • vecMulVec v (star v)) :
    ρ = ptrB ρ ⊗ₖ ptrA ρ := by
  set P := c • vecMulVec v (star v) with hPdef
  have hP2 : P * P = P := rankOne_mul_self hc
  have hPh : Pᴴ = P := rankOne_conjTranspose hcs v
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hP2, sub_self, sub_zero]
  set R := (1 - P) ⊗ₖ (1 : Matrix μ μ ℂ) with hRdef
  have hRh : Rᴴ = R := by
    rw [hRdef, conjTranspose_kronecker, conjTranspose_sub, conjTranspose_one, conjTranspose_one, hPh]
  have hR2 : R * R = R := by
    rw [hRdef, ← mul_kronecker_mul, hQ, Matrix.mul_one]
  have htr : trace (ρ * R) = 0 := by
    rw [hRdef, ← trace_ptrB_mul, hpure, mul_sub, Matrix.mul_one, hP2, sub_self, trace_zero]
  have hρR : ρ * R = 0 := mul_eq_zero_of_trace_mul_eq_zero hρ hRh hR2 htr
  have hRρ : R * ρ = 0 := by
    have h := congrArg conjTranspose hρR
    rwa [conjTranspose_mul, hRh, hρ.1.eq, conjTranspose_zero] at h
  have hsum : P ⊗ₖ (1 : Matrix μ μ ℂ) + R = 1 := by
    have h1 : P + (1 - P) = 1 := by abel
    rw [hRdef, ← add_kronecker, h1, one_kronecker_one]
  have e1 : ρ * (P ⊗ₖ (1 : Matrix μ μ ℂ)) = ρ := by
    calc ρ * (P ⊗ₖ (1 : Matrix μ μ ℂ)) = ρ * (P ⊗ₖ (1 : Matrix μ μ ℂ)) + ρ * R := by
          rw [hρR, add_zero]
      _ = ρ := by rw [← Matrix.mul_add, hsum, Matrix.mul_one]
  have e2 : (P ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ = ρ := by
    calc (P ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ = (P ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ + R * ρ := by
          rw [hRρ, add_zero]
      _ = ρ := by rw [← Matrix.add_mul, hsum, Matrix.one_mul]
  have hρP : ρ = (P ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ * (P ⊗ₖ (1 : Matrix μ μ ℂ)) := by
    rw [e2, e1]
  set X : Matrix μ μ ℂ := Matrix.of fun a b => ∑ n, ∑ n', (star v) n * ρ (n, a) (n', b) * v n'
    with hXdef
  have hL : (P ⊗ₖ (1 : Matrix μ μ ℂ)) * ρ * (P ⊗ₖ (1 : Matrix μ μ ℂ)) =
      (c * c) • (vecMulVec v (star v) ⊗ₖ X) := by
    rw [hPdef]
    simp only [smul_kronecker, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [rankOne_kron_one_conj]
  have hR' : P ⊗ₖ (c • X) = (c * c) • (vecMulVec v (star v) ⊗ₖ X) := by
    rw [hPdef, smul_kronecker, kronecker_smul, smul_smul]
  have hblock : ρ = P ⊗ₖ (c • X) := hρP.trans (hL.trans hR'.symm)
  have hA : ptrA ρ = c • X := by
    conv_lhs => rw [hblock]
    rw [ptrA_kronecker, hPdef, trace_rankOne hc, one_smul]
  rw [hpure, hA]
  exact hblock

/-! ## A 與 C 不相關 -/

/-- 三方態 `ρ_ABC`（指標 `(ι × κ) × μ`）跡掉中間的 B，得到 `ρ_AC`（指標 `ι × μ`）。 -/
def ptrMid {ι κ ξ : Type*} [Fintype κ] (X : Matrix ((ι × κ) × ξ) ((ι × κ) × ξ) ℂ) :
    Matrix (ι × ξ) (ι × ξ) ℂ :=
  Matrix.of fun p q => ∑ b, X ((p.1, b), p.2) ((q.1, b), q.2)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq μ] [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype μ] in
theorem ptrMid_kronecker (A : Matrix (ι × κ) (ι × κ) ℂ) (C : Matrix μ μ ℂ) :
    ptrMid (A ⊗ₖ C) = ptrB A ⊗ₖ C := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [ptrMid, Matrix.of_apply, kroneckerMap_apply, ptrB_apply, Finset.sum_mul]

omit [DecidableEq μ] [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype μ] in
/-- 保真：`Tr_B((A ⊗ B) ⊗ C) = (tr B)·(A ⊗ C)`，跡掉的確實是中間那一個。 -/
theorem ptrMid_kronecker3 (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (C : Matrix μ μ ℂ) :
    ptrMid ((A ⊗ₖ B) ⊗ₖ C) = trace B • (A ⊗ₖ C) := by
  rw [ptrMid_kronecker, ptrB_kronecker, smul_kronecker]

/-- **A 與 C 不相關**：AB 的邊際是純態時，`ρ_AC = ρ_A ⊗ ρ_C`，互資訊 `S(A) + S(C) − S(AC) = 0`。 -/
theorem monogamy_mutualInfo {ρ : Matrix ((ι × κ) × μ) ((ι × κ) × μ) ℂ} (hρ : ρ.PosSemidef)
    {c : ℂ} {v : ι × κ → ℂ} (hcs : star c = c) (hc : c * ∑ i, star (v i) * v i = 1)
    (hpure : ptrB ρ = c • vecMulVec v (star v)) :
    ptrMid ρ = ptrB (ptrB ρ) ⊗ₖ ptrA ρ ∧
      vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA ρ) - vnEntropy (ptrMid ρ) = 0 := by
  have hm := monogamy hρ hcs hc hpure
  have hmid : ptrMid ρ = ptrB (ptrB ρ) ⊗ₖ ptrA ρ := by
    conv_lhs => rw [hm]
    rw [ptrMid_kronecker]
  refine ⟨hmid, ?_⟩
  have hAB := ptrB_posSemidef hρ
  have htrAB : trace (ptrB ρ) = 1 := by rw [hpure, trace_rankOne hc]
  have hA := ptrB_posSemidef hAB
  have htrA : trace (ptrB (ptrB ρ)) = 1 := by rw [trace_ptrB, htrAB]
  have hC := ptrA_posSemidef hρ
  have htrC : trace (ptrA ρ) = 1 := by rw [trace_ptrA, ← trace_ptrB, htrAB]
  rw [hmid, vnEntropy_kronecker hA.1 hC.1 htrA htrC]
  ring

/-! ## Bell 實例 -/

theorem maxEnt_posSemidef : (maxEnt (Fin 2)).PosSemidef := by
  rw [maxEnt_eq_disentangle_conj, star_eq_conjTranspose]
  exact (ket0Proj_posSemidef.kronecker ket0Proj_posSemidef).mul_mul_conjTranspose_same _

theorem trace_maxEnt : trace (maxEnt (Fin 2)) = 1 := by
  rw [← trace_ptrB, ptrB_bell_eq_mix2, trace_mix2]

/-- Bell 態寫成 `c·|v⟩⟨v|`：`c = 1/2`、`v = |00⟩ + |11⟩`，`c·⟨v, v⟩ = 1`。 -/
theorem bell_rankOne_norm :
    ((Fintype.card (Fin 2) : ℂ))⁻¹ *
      ∑ i, star (vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ) i) * vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ) i = 1 := by
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

/-- **Bell 實例**：AB 的邊際是 Bell 態時，`ρ_ABC = Bell ⊗ ρ_C`；A 與 B 的互資訊 `2 ln 2`，
A 與 C 的互資訊 0。 -/
theorem bell_monogamy {ρ : Matrix ((Fin 2 × Fin 2) × μ) ((Fin 2 × Fin 2) × μ) ℂ}
    (hρ : ρ.PosSemidef) (hbell : ptrB ρ = maxEnt (Fin 2)) :
    ρ = maxEnt (Fin 2) ⊗ₖ ptrA ρ ∧
      vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA (ptrB ρ)) - vnEntropy (ptrB ρ) = 2 * Real.log 2 ∧
      vnEntropy (ptrB (ptrB ρ)) + vnEntropy (ptrA ρ) - vnEntropy (ptrMid ρ) = 0 := by
  have hcs : star ((Fintype.card (Fin 2) : ℂ))⁻¹ = ((Fintype.card (Fin 2) : ℂ))⁻¹ := by simp
  have hpure : ptrB ρ = ((Fintype.card (Fin 2) : ℂ))⁻¹ •
      vecMulVec (vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ)) (star (vecOf (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [hbell]
    rfl
  have hm := monogamy hρ hcs bell_rankOne_norm hpure
  rw [hbell] at hm
  refine ⟨hm, ?_, (monogamy_mutualInfo hρ hcs bell_rankOne_norm hpure).2⟩
  rw [hbell]
  exact bell_mutual_information

/-- 假設可以滿足：`Bell ⊗ |0⟩⟨0|` 半正定，AB 的邊際是 Bell 態。 -/
theorem bell_monogamy_witness :
    (maxEnt (Fin 2) ⊗ₖ ket0Proj).PosSemidef ∧ ptrB (maxEnt (Fin 2) ⊗ₖ ket0Proj) = maxEnt (Fin 2) := by
  refine ⟨maxEnt_posSemidef.kronecker ket0Proj_posSemidef, ?_⟩
  rw [ptrB_kronecker, trace_ket0Proj, one_smul]

/-- **負控制**：邊際不是純態時結論失敗。Bell 態看成「一個 qubit（當 AB）加 C」：
邊際是混合態，而整體不是乘積（`S(ρ) = 0`，乘積的熵是 `2 ln 2`）。 -/
theorem negctrl_monogamy_mixed :
    ¬ (maxEnt (Fin 2) = ptrB (maxEnt (Fin 2)) ⊗ₖ ptrA (maxEnt (Fin 2))) := by
  intro h
  have h1 := congrArg vnEntropy h
  rw [vnEntropy_bell, ptrB_bell_eq_mix2, ptrA_maxEnt, ← ptrB_maxEnt, ptrB_bell_eq_mix2,
    vnEntropy_kronecker mix2_posSemidef.1 mix2_posSemidef.1 trace_mix2 trace_mix2,
    vnEntropy_mix2] at h1
  linarith [Real.log_pos one_lt_two]

end

end ErEpr
