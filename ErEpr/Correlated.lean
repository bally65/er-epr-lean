import ErEpr.Landauer

/-!
# ErEpr.Correlated：糾纏的起點——條件熵為負、Landauer 的乘積假設拿不掉

兩件事用**同一個**解糾纏的么正矩陣 `D`（`disentangle`）證，它把 Bell 態 `(|00⟩ + |11⟩)/√2`
（本庫的 `maxEnt (Fin 2)`）轉到 `|00⟩`：`D·Bell·Dᴴ = |0⟩⟨0| ⊗ |0⟩⟨0|`（`disentangle_conj_maxEnt`）。

* **Bell 態 `S(AB) = 0 < S(A) = ln 2`**：
  * `S(Bell) = S(|00⟩⟨00|) = 0`（`vnEntropy_bell`，么正不變＋張量積可加）；
  * 兩側的約化態都是最大混合態，熵 `ln 2`（`vnEntropy_ptrB_bell`、`vnEntropy_ptrA_bell`）；
  * 所以條件熵 `S(AB) − S(B) = −ln 2 < 0`（`bell_conditional_entropy`），互資訊是 `2 ln 2`
    （`bell_mutual_information`，次可加性在這裡離等號最遠）；
  * 古典分佈的 `S(A) ≤ S(AB)` 在這裡失敗（`negctrl_entropy_monotone`）。對照：對角（古典）
    聯合分佈確實滿足它（`vnEntropy_ptrB_diagonal_le`），所以失敗的原因是糾纏。
* **Landauer 的乘積假設拿不掉**（`correlation_is_fuel`）：熱庫取 `H = 0`（任何溫度的 Gibbs 態都是
  最大混合態，熱庫的能量恆為 0），系統與熱庫的**邊際態完全相同**，只差起點有沒有相關：
  * 乘積起點 `mix2 ⊗ γ`：任何么正演化之後，系統的熵都還至少是 `ln 2`（`landauer` 的推論
    `product_start_no_erasure`）；
  * Bell 起點：`D` 一步就把系統變成純態，熵少了 `ln 2`，熱是 0。
  寫成 `landauer` 的形狀就是 `negctrl_landauer_correlated`：系統熵減少 `ln 2 > 0 = β·Q`。

物理讀法：與熱庫的糾纏可以當成抹除的燃料（del Rio、Åberg、Renner、Dahlsten、Vedral，
Nature 2011；DOI 未核對）。這正是 EPR 那一側的資源出現在熱力學裡的地方。

範圍（引用前請讀）：
* 只有一個 2×2 的例子；沒有證「相關起點時 Landauer 的修正項是互資訊」這類一般陳述。
* `H = 0` 讓「熱」恆為 0，所以負控制的內容全在「系統的熵能不能降」，不在熱的大小。
* 定理陳述只談矩陣與實數；物理名詞只出現在說明文字裡。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder Real

noncomputable section

/-! ## 解糾纏的么正矩陣 -/

/-- Bell 基底的整數矩陣：四列依序是 `Φ⁺, Ψ⁺, Ψ⁻, Φ⁻` 乘上 `√2`，
即 `(1,0,0,1)`、`(0,1,1,0)`、`(0,1,−1,0)`、`(1,0,0,−1)`。它是對稱的，`K² = 2`。 -/
def bellK : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if (p.1 = p.2 ↔ q.1 = q.2) then (if p.1 = 1 ∧ q.1 = 1 then -1 else 1) else 0

theorem star_bellK : star bellK = bellK := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.star_apply]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;> simp [bellK]

theorem bellK_mul_self : bellK * bellK = (2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [bellK, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- `K·Bell·K = 2·|00⟩⟨00|`：`K` 把 `|00⟩ + |11⟩` 送到 `2|00⟩`。 -/
theorem bellK_conj_maxEnt :
    bellK * maxEnt (Fin 2) * bellK = (2 : ℂ) • (ket0Proj ⊗ₖ ket0Proj) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [bellK, maxEnt, ket0Proj, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      vecMulVec_apply, kroneckerMap_apply]

theorem sBell_mul_self_complex : (sBell : ℂ) * (sBell : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, sBell_mul_self]
  norm_num

/-- 解糾纏的么正矩陣 `D = K/√2`：`D|Φ⁺⟩ = |00⟩`。 -/
def disentangle : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (sBell : ℂ) • bellK

theorem star_disentangle : star disentangle = disentangle := by
  rw [disentangle, star_smul, star_bellK, Complex.star_def, Complex.conj_ofReal]

theorem disentangle_mul_self : disentangle * disentangle = 1 := by
  rw [disentangle, Matrix.smul_mul, Matrix.mul_smul, smul_smul, bellK_mul_self, smul_smul,
    sBell_mul_self_complex]
  norm_num

/-- `D` 是么正矩陣。 -/
theorem disentangle_star_mul : star disentangle * disentangle = 1 := by
  rw [star_disentangle, disentangle_mul_self]

/-- **解糾纏**：`D·Bell·Dᴴ = |0⟩⟨0| ⊗ |0⟩⟨0|`。 -/
theorem disentangle_conj_maxEnt :
    disentangle * maxEnt (Fin 2) * star disentangle = ket0Proj ⊗ₖ ket0Proj := by
  rw [star_disentangle, disentangle, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    bellK_conj_maxEnt, smul_smul, sBell_mul_self_complex]
  norm_num

/-- 反過來：`Bell = D·|00⟩⟨00|·Dᴴ`。 -/
theorem maxEnt_eq_disentangle_conj :
    maxEnt (Fin 2) = disentangle * (ket0Proj ⊗ₖ ket0Proj) * star disentangle := by
  rw [← disentangle_conj_maxEnt, star_disentangle]
  simp only [← Matrix.mul_assoc, disentangle_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, disentangle_mul_self, Matrix.mul_one]

/-! ## Bell 態：S(AB) = 0 < S(A) = ln 2 -/

/-- **Bell 態是純態**：`S(Bell) = 0`。 -/
theorem vnEntropy_bell : vnEntropy (maxEnt (Fin 2)) = 0 := by
  rw [maxEnt_eq_disentangle_conj, vnEntropy_unitary_conj _ _ disentangle_star_mul,
    vnEntropy_kronecker ket0Proj_posSemidef.1 ket0Proj_posSemidef.1 trace_ket0Proj trace_ket0Proj,
    vnEntropy_ket0Proj, add_zero]

theorem vnEntropy_ptrB_bell : vnEntropy (ptrB (maxEnt (Fin 2))) = Real.log 2 := by
  rw [vnEntropy_ptrB_maxEnt, Fintype.card_fin, Nat.cast_ofNat]

theorem vnEntropy_ptrA_bell : vnEntropy (ptrA (maxEnt (Fin 2))) = Real.log 2 := by
  rw [ptrA_maxEnt, ← ptrB_maxEnt, vnEntropy_ptrB_bell]

/-- **條件熵為負**：`S(A|B) = S(AB) − S(B) = −ln 2`。 -/
theorem bell_conditional_entropy :
    vnEntropy (maxEnt (Fin 2)) - vnEntropy (ptrA (maxEnt (Fin 2))) = -Real.log 2 := by
  rw [vnEntropy_bell, vnEntropy_ptrA_bell, zero_sub]

/-- 互資訊 `S(A) + S(B) − S(AB) = 2 ln 2`：次可加性在 Bell 態離等號最遠。 -/
theorem bell_mutual_information :
    vnEntropy (ptrB (maxEnt (Fin 2))) + vnEntropy (ptrA (maxEnt (Fin 2))) -
      vnEntropy (maxEnt (Fin 2)) = 2 * Real.log 2 := by
  rw [vnEntropy_bell, vnEntropy_ptrB_bell, vnEntropy_ptrA_bell]
  ring

/-- **負控制**：古典的 `S(A) ≤ S(AB)` 在 Bell 態失敗。 -/
theorem negctrl_entropy_monotone :
    ¬ (vnEntropy (ptrB (maxEnt (Fin 2))) ≤ vnEntropy (maxEnt (Fin 2))) := by
  rw [vnEntropy_ptrB_bell, vnEntropy_bell, not_le]
  exact Real.log_pos one_lt_two

/-! ## 古典對照：對角聯合分佈滿足 S(A) ≤ S(AB) -/

/-- `−x log x` 的次可加：非負數 `q_k` 滿足 `η(Σ q) ≤ Σ η(q)`（由 `log` 單調）。 -/
theorem negMulLog_sum_le {κ : Type*} [Fintype κ] (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k) :
    Real.negMulLog (∑ k, q k) ≤ ∑ k, Real.negMulLog (q k) := by
  have hS : ∀ k, q k ≤ ∑ j, q j := fun k =>
    Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ k)
  have hterm : ∀ k, q k * Real.log (q k) ≤ q k * Real.log (∑ j, q j) := by
    intro k
    rcases (hq k).eq_or_lt with h | h
    · rw [← h]
      simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (hS k)) (hq k)
  have hsum : ∑ k, q k * Real.log (q k) ≤ (∑ k, q k) * Real.log (∑ j, q j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hterm k
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **古典對照**：對角（古典）聯合分佈 `p ≥ 0` 滿足 `S(A) ≤ S(AB)`。 -/
theorem vnEntropy_ptrB_diagonal_le (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) :
    vnEntropy (ptrB (diagonal fun x => (p x : ℂ))) ≤ vnEntropy (diagonal fun x => (p x : ℂ)) := by
  have hB : ptrB (diagonal fun x => (p x : ℂ)) = diagonal fun i => ((∑ k, p (i, k) : ℝ) : ℂ) := by
    ext i j
    rw [ptrB_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hB, vnEntropy_diagonal, vnEntropy_diagonal, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun i _ => negMulLog_sum_le (fun k => p (i, k)) (fun k => hp (i, k))

/-! ## Landauer 的乘積假設拿不掉 -/

/-- `H = 0` 的 Gibbs 態：任何溫度都是最大混合態。 -/
theorem gibbs_zero_ham (β : ℝ) :
    gibbs (0 : Matrix ι ι ℂ) β = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  rw [gibbs, smul_zero, NormedSpace.exp_zero, trace_one]
  push_cast
  rfl

/-- **乘積起點**：熱庫 `H = 0` 時，任何么正演化都不能降低系統的熵（`landauer` 的推論）。 -/
theorem product_start_no_erasure [Nonempty κ] {ρS : Matrix ι ι ℂ} (hρS : ρS.PosSemidef)
    (htrS : trace ρS = 1) {β : ℝ} (hβ : 0 ≤ β) {U : Matrix (ι × κ) (ι × κ) ℂ}
    (hU : star U * U = 1) :
    vnEntropy ρS ≤ vnEntropy (ptrB (U * (ρS ⊗ₖ gibbs (0 : Matrix κ κ ℂ) β) * star U)) :=
  no_heatless_erasure hρS htrS isHermitian_zero hβ hU (by simp)

/-- Bell 態的熱庫那一側恰好是 `H = 0` 的 Gibbs 態。 -/
theorem ptrA_bell_eq_gibbs (β : ℝ) :
    ptrA (maxEnt (Fin 2)) = gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β := by
  rw [ptrA_maxEnt, gibbs_zero_ham]
  push_cast
  rfl

/-- Bell 態的系統那一側是 `mix2`。 -/
theorem ptrB_bell_eq_mix2 : ptrB (maxEnt (Fin 2)) = mix2 := by
  rw [ptrB_maxEnt]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mix2]

/-- 解糾纏之後系統是純態 `|0⟩⟨0|`。 -/
theorem ptrB_disentangle_bell :
    ptrB (disentangle * maxEnt (Fin 2) * star disentangle) = ket0Proj := by
  rw [disentangle_conj_maxEnt, ptrB_kronecker, trace_ket0Proj, one_smul]

/-- **糾纏是燃料**：系統與熱庫（`H = 0`）的邊際態完全相同，
* 乘積起點 `mix2 ⊗ γ`：任何么正演化之後系統的熵仍至少 `ln 2`；
* Bell 起點：么正矩陣 `D` 把系統變成純態，熵是 0。 -/
theorem correlation_is_fuel {β : ℝ} (hβ : 0 ≤ β) :
    (ptrB (maxEnt (Fin 2)) = ptrB (mix2 ⊗ₖ gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β) ∧
      ptrA (maxEnt (Fin 2)) = ptrA (mix2 ⊗ₖ gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β)) ∧
    (∀ U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, star U * U = 1 →
      Real.log 2 ≤
        vnEntropy (ptrB (U * (mix2 ⊗ₖ gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β) * star U))) ∧
    star disentangle * disentangle = 1 ∧
      vnEntropy (ptrB (disentangle * maxEnt (Fin 2) * star disentangle)) = 0 := by
  refine ⟨⟨?_, ?_⟩, fun U hU => ?_, disentangle_star_mul, ?_⟩
  · rw [ptrB_kronecker, trace_gibbs isHermitian_zero, one_smul, ptrB_bell_eq_mix2]
  · rw [ptrA_kronecker, trace_mix2, one_smul, ptrA_bell_eq_gibbs]
  · rw [← vnEntropy_mix2]
    exact product_start_no_erasure mix2_posSemidef trace_mix2 hβ hU
  · rw [ptrB_disentangle_bell, vnEntropy_ket0Proj]

/-- **負控制**：Landauer 的「乘積起點」拿不掉。Bell 起點（熱庫那一側仍是 Gibbs 態）
經 `D` 之後，系統的熵少了 `ln 2`，`β·Q = 0`。 -/
theorem negctrl_landauer_correlated (β : ℝ) :
    ptrA (maxEnt (Fin 2)) = gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β ∧
      ¬ (vnEntropy (ptrB (maxEnt (Fin 2))) -
            vnEntropy (ptrB (disentangle * maxEnt (Fin 2) * star disentangle)) ≤
          β * ((trace (ptrA (disentangle * maxEnt (Fin 2) * star disentangle) *
            (0 : Matrix (Fin 2) (Fin 2) ℂ))).re -
            (trace (gibbs (0 : Matrix (Fin 2) (Fin 2) ℂ) β * 0)).re)) := by
  refine ⟨ptrA_bell_eq_gibbs β, ?_⟩
  rw [ptrB_disentangle_bell, vnEntropy_ptrB_bell, vnEntropy_ket0Proj, Matrix.mul_zero,
    Matrix.mul_zero, trace_zero, Complex.zero_re, sub_zero, sub_self, mul_zero, not_le]
  exact Real.log_pos one_lt_two

end

end ErEpr
