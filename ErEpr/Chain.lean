import ErEpr.NoSignalling
import ErEpr.NoGo
import ErEpr.Hawking

/-!
# ErEpr.Chain：兩欄之間的組合與耦合

* **T1∘T2**（`ptrB_idKron_tfdState`）：對 TFD 的 B 側施任何保跡映射，A 側仍是 Gibbs 態。
  一行：`ptrB_idKron`（T1）接 `ptrB_tfdState`（T2a）。
* **耦合版不可能定理**：把 EPR 側的 `no_finite_dim_gibbs_matches_bh_mass` 接上 ER 側的錨點。
  * `no_gibbs_matches_unitConeAngle`：β 由單位錐角條件決定（用 `hawking_beta`）；
  * `no_gibbs_matches_first_law`：β 與 S 都只假設 `first_law_area` 的前提
    （用 `first_law_area` 與 `hawking_beta`），不直接寫 `8πM` 或 `4πM²`。
  只擾動 ER 側（例如把 `hawking_beta` 的 `8πM` 改成 `4πM`），這兩條就會斷。

範圍（引用前請讀）：
* 耦合版的限定與 `ErEpr/NoGo.lean` 相同：只對比熱為負的漸近平坦 Schwarzschild；
  AdS 大黑洞比熱為正，不適用。
* 這不是對 ER=EPR 的反駁，是對「黑洞 = 固定有限維正則系綜」這種識別法的排除。
* 單位錐角條件只是視界光滑的一階必要條件（見 `ErEpr/Hawking.lean`）。
-/

namespace ErEpr

open Matrix
open scoped Real

noncomputable section

variable {ι κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ'] {H : Matrix ι ι ℂ}

/-- **T1∘T2**：對 TFD 的 B 側施任何 ℂ-線性保跡映射 `Φ`，A 側的約化態仍是 Gibbs 態。 -/
theorem ptrB_idKron_tfdState (hH : H.IsHermitian) (β : ℝ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ' κ' ℂ) (hTP : ∀ M, trace (Φ M) = trace M) :
    ptrB (idKron Φ (tfdState hH β)) = gibbs H β := by
  rw [ptrB_idKron Φ hTP, ptrB_tfdState]

/-- **耦合版（單位錐角）**：不可能對所有 `M ∈ (a, b)` 都找到滿足單位錐角條件的 β，
使 `S(gibbs H β) = 4πM²`。β 不是直接寫成 `8πM`，而是由 `hawking_beta` 從單位錐角條件解出。
限定：只對比熱為負的漸近平坦 Schwarzschild；AdS 大黑洞不適用；
不是對 ER=EPR 的反駁，是對「黑洞 = 固定有限維正則系綜」這種識別法的排除。 -/
theorem no_gibbs_matches_unitConeAngle [Nonempty ι] (hH : H.IsHermitian) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ¬ ∀ M ∈ Set.Ioo a b, ∃ β, UnitConeAngle M β ∧ vnEntropy (gibbs H β) = 4 * π * M ^ 2 := by
  intro h
  refine no_finite_dim_gibbs_matches_bh_mass hH ha hab fun M hM => ?_
  obtain ⟨β, hβ, hS⟩ := h M hM
  rwa [(hawking_beta (ha.trans hM.1)).mp hβ] at hS

/-- **耦合版（第一定律）**：設 `S, β` 滿足 `first_law_area` 的全部前提
（`S(0) = 0`、`dS/dm = β(m)`、每個 `m > 0` 都滿足單位錐角條件）。
則不可能對所有 `M ∈ (a, b)` 都有 `S(gibbs H (β M)) = S(M)`。
證明用到 `hawking_beta`（β = 8πM）與 `first_law_area`（S = 4πM²），再接 EPR 側的不可能定理。
限定：只對比熱為負的漸近平坦 Schwarzschild；AdS 大黑洞不適用；
不是對 ER=EPR 的反駁，是對「黑洞 = 固定有限維正則系綜」這種識別法的排除。 -/
theorem no_gibbs_matches_first_law [Nonempty ι] (hH : H.IsHermitian) {S β : ℝ → ℝ}
    (h0 : S 0 = 0) (hS : ∀ m, HasDerivAt S (β m) m) (hβ : ∀ m, 0 < m → UnitConeAngle m (β m))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ¬ ∀ M ∈ Set.Ioo a b, vnEntropy (gibbs H (β M)) = S M := by
  intro h
  refine no_finite_dim_gibbs_matches_bh_mass hH ha hab fun M hM => ?_
  have hM0 : 0 < M := ha.trans hM.1
  rw [← (hawking_beta hM0).mp (hβ M hM0), h M hM, (first_law_area h0 hS hβ hM0).1]

end

end ErEpr
