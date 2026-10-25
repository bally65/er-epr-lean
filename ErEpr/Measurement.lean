import ErEpr.Correlated
import ErEpr.NoSignalling

/-!
# ErEpr.Measurement：觀測＝把線轉給儀器（退相干的最小模型）

系統 qubit 在疊加態 `|+⟩ = (|0⟩ + |1⟩)/√2`（`plusProj = |+⟩⟨+|`，干涉項 `1/2`），
儀器 qubit 在 `|0⟩`。測量的交互作用是 CNOT（`cnot`，系統控制、儀器被翻）：
`CNOT (|+⟩⟨+| ⊗ |0⟩⟨0|) CNOTᴴ = Bell`（`cnot_measure`）。

* **只看系統，線像是脫落了**（`measurement_dephases`、`measurement_entropy`）：
  系統約化態的干涉項 `1/2 → 0`，對角（出現機率）不變，熵 `0 → ln 2`。
* **整體的線還在**：系統＋儀器在測量前後都是純態，熵都是 0。兩條路算出同一個 0：
  測量前用 `|+⟩⟨+|` 是秩一（`vnEntropy_plusProj`，不經 Bell），測量後用解糾纏矩陣
  （`vnEntropy_bell`）；兩者一致正是么正不變的要求（`measurement_total_entropy_conserved`）。
* **只動一端解不開**：
  * 只動系統：任何么正 `U ⊗ 1` 之後，系統的熵仍是 `ln 2`（`local_cannot_undo`，
    由 `Tr_B((U ⊗ 1) X (U ⊗ 1)ᴴ) = U·Tr_B X·Uᴴ`，`ptrB_local_conj`，任何維度都成立）；
  * 只動儀器：任何 Kraus 通道（不只么正）之後，系統的約化態完全不變，熵仍是 `ln 2`
    （`pointer_cannot_undo`，就是既有的不可通訊定理 `Kraus.no_signalling`）。
* **兩端一起才解得開**（`joint_undo`）：解糾纏矩陣 `D` 讓系統回到純態；再做一次 CNOT
  則完全還原 `|+⟩⟨+| ⊗ |0⟩⟨0|`，干涉項回到 `1/2`。
* 負控制 `negctrl_local_no_decoherence`：交互作用若只動系統（`U ⊗ 1`，不糾纏），
  系統的熵仍是 0：沒有糾纏就沒有退相干。

範圍（引用前請讀）：
* 這是退相干的 2×2 玩具：只有一個系統 qubit、一個儀器 qubit、一次交互作用。
  「坍縮」在這裡的意思只是「系統的約化態變成對角」；本檔不談詮釋問題
  （哥本哈根、多世界等），也沒有證明「觀測者」是什麼。
* 因果沒有被觀測剪斷：只動儀器改變不了系統的約化態（不可通訊）。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder Real

noncomputable section

/-! ## 系統的疊加態與 CNOT -/

/-- `|+⟩⟨+| = (1/2)·[[1, 1], [1, 1]]`。 -/
def plusProj : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ _ => (1 / 2 : ℂ)

theorem plusProj_isHermitian : plusProj.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusProj]

theorem plusProj_mul_self : plusProj * plusProj = plusProj := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plusProj, Matrix.mul_apply, Fin.sum_univ_two]

theorem plusProj_posSemidef : plusProj.PosSemidef := by
  have h : plusProj = plusProj * plusProjᴴ := by
    rw [plusProj_isHermitian.eq, plusProj_mul_self]
  rw [h]
  exact posSemidef_self_mul_conjTranspose _

theorem trace_plusProj : trace plusProj = 1 := by
  rw [trace, Fin.sum_univ_two]
  norm_num [plusProj]

/-- `|+⟩⟨+|` 是純態：`S = 0`。證法：寫成 `(2×1)(1×2)`，再用 `S(AB) = S(BA)` 換成 1×1 的 `[1]`。
不經 Bell 態。 -/
theorem vnEntropy_plusProj : vnEntropy plusProj = 0 := by
  have h : plusProj = (Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 / 2 : ℂ)) *
      (Matrix.of fun (_ : Fin 1) (_ : Fin 2) => (1 : ℂ)) := by
    ext i j
    simp [plusProj, Matrix.mul_apply]
  have h1 : (Matrix.of fun (_ : Fin 1) (_ : Fin 2) => (1 : ℂ)) *
      (Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 / 2 : ℂ)) =
      ((1 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h, vnEntropy_mul_comm, h1, vnEntropy_smul_one, Real.negMulLog_one, mul_zero]

/-- CNOT：系統（左因子）控制、儀器（右因子）被翻，`|i, k⟩ ↦ |i, i ⊕ k⟩`。 -/
def cnot : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ (p.2 = q.2 ↔ q.1 = 0) then 1 else 0

theorem star_cnot : star cnot = cnot := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.star_apply]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;> simp [cnot]

theorem cnot_mul_self : cnot * cnot = 1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- CNOT 是么正矩陣。 -/
theorem cnot_star_mul : star cnot * cnot = 1 := by
  rw [star_cnot, cnot_mul_self]

/-- **測量**：`CNOT (|+⟩⟨+| ⊗ |0⟩⟨0|) CNOTᴴ = Bell`。 -/
theorem cnot_measure : cnot * (plusProj ⊗ₖ ket0Proj) * star cnot = maxEnt (Fin 2) := by
  rw [star_cnot]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [cnot, plusProj, ket0Proj, maxEnt, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, kroneckerMap_apply, vecMulVec_apply]

theorem ptrB_before : ptrB (plusProj ⊗ₖ ket0Proj) = plusProj := by
  rw [ptrB_kronecker, trace_ket0Proj, one_smul]

theorem ptrB_after : ptrB (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) = mix2 := by
  rw [cnot_measure, ptrB_bell_eq_mix2]

/-! ## 只看系統：干涉項歸零、熵 0 → ln 2；整體仍是純態 -/

/-- **干涉項歸零、機率不變**：測量前系統的干涉項是 `1/2`，測量後是 0；對角不變。 -/
theorem measurement_dephases :
    (ptrB (plusProj ⊗ₖ ket0Proj)) 0 1 = 1 / 2 ∧
      (ptrB (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot)) 0 1 = 0 ∧
      ∀ i, (ptrB (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot)) i i =
        (ptrB (plusProj ⊗ₖ ket0Proj)) i i := by
  rw [ptrB_before, ptrB_after]
  refine ⟨by simp [plusProj], by simp [mix2], fun i => ?_⟩
  fin_cases i <;> norm_num [mix2, plusProj]

/-- **熵**：系統 `0 → ln 2`，整體 `0 → 0`。 -/
theorem measurement_entropy :
    vnEntropy (ptrB (plusProj ⊗ₖ ket0Proj)) = 0 ∧ vnEntropy (plusProj ⊗ₖ ket0Proj) = 0 ∧
      vnEntropy (ptrB (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot)) = Real.log 2 ∧
      vnEntropy (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ptrB_before, vnEntropy_plusProj]
  · rw [vnEntropy_kronecker plusProj_isHermitian ket0Proj_posSemidef.1 trace_plusProj
      trace_ket0Proj, vnEntropy_plusProj, vnEntropy_ket0Proj, add_zero]
  · rw [ptrB_after, vnEntropy_mix2]
  · rw [cnot_measure, vnEntropy_bell]

/-- 交叉檢查：整體熵在測量前後相同（么正不變）。測量後那一邊的 0 由 Bell 態算出，
測量前那一邊的 0 由秩一算出，兩條路獨立。 -/
theorem measurement_total_entropy_conserved :
    vnEntropy (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) = vnEntropy (plusProj ⊗ₖ ket0Proj) :=
  vnEntropy_unitary_conj _ _ cnot_star_mul

/-! ## 只動一端解不開；兩端一起才解得開 -/

/-- 只動系統：`Tr_B((U ⊗ 1) X (U ⊗ 1)ᴴ) = U·Tr_B X·Uᴴ`，任何維度。 -/
theorem ptrB_local_conj {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ptrB ((U ⊗ₖ (1 : Matrix κ κ ℂ)) * X * star (U ⊗ₖ (1 : Matrix κ κ ℂ))) = U * ptrB X * star U := by
  rw [star_kronecker, star_one]
  ext i j
  simp only [ptrB_apply, Matrix.mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **只動系統解不開**：測量之後，對系統做任何么正演化，它的熵仍是 `ln 2`。 -/
theorem local_cannot_undo {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : star U * U = 1) :
    vnEntropy (ptrB ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) *
        star (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = Real.log 2 := by
  rw [ptrB_local_conj, vnEntropy_unitary_conj _ _ hU, ptrB_after, vnEntropy_mix2]

/-- **只動儀器解不開**：對儀器做任何 Kraus 通道，系統的約化態完全不變（不可通訊），熵仍是 `ln 2`。 -/
theorem pointer_cannot_undo {r : Type*} [Fintype r] (Φ : Kraus (Fin 2) r) :
    vnEntropy (ptrB (Φ.app (Fin 2) (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot))) = Real.log 2 := by
  rw [Kraus.no_signalling, ptrB_after, vnEntropy_mix2]

/-- **兩端一起才解得開**：解糾纏矩陣 `D` 讓系統回到純態；再做一次 CNOT 則完全還原，
干涉項回到 `1/2`。 -/
theorem joint_undo :
    vnEntropy (ptrB (disentangle * (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) *
        star disentangle)) = 0 ∧
      cnot * (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) * star cnot = plusProj ⊗ₖ ket0Proj ∧
      (ptrB (cnot * (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) * star cnot)) 0 1 = 1 / 2 := by
  have hback : cnot * (cnot * (plusProj ⊗ₖ ket0Proj) * star cnot) * star cnot =
      plusProj ⊗ₖ ket0Proj := by
    rw [star_cnot]
    simp only [← Matrix.mul_assoc, cnot_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, cnot_mul_self, Matrix.mul_one]
  refine ⟨?_, hback, ?_⟩
  · rw [cnot_measure, ptrB_disentangle_bell, vnEntropy_ket0Proj]
  · rw [hback, ptrB_before]
    simp [plusProj]

/-- **負控制**：交互作用若只動系統（`U ⊗ 1`，不糾纏），系統的熵仍是 0：沒有糾纏就沒有退相干。 -/
theorem negctrl_local_no_decoherence {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : star U * U = 1) :
    vnEntropy (ptrB ((U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (plusProj ⊗ₖ ket0Proj) *
      star (U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))) = 0 := by
  rw [ptrB_local_conj, vnEntropy_unitary_conj _ _ hU, ptrB_before, vnEntropy_plusProj]

end

end ErEpr
