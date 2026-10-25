import ErEpr.TensorNetwork
import ErEpr.Entropy

/-!
# ErEpr.MinCut：圖對態的約束（B4：G6、G5、G1、G2、G4）

沿用 `TensorNetwork.lean` 的圖：頂點 `V`、邊 `E`、端點 `ends e : V × V`，割邊 `cutEdges ends W`
（恰有一端在 `W` 的邊）。

* **G6 割函數的次模性**（`cutEdges_card_submodular`）：
  `|δ(W ∪ W′)| + |δ(W ∩ W′)| ≤ |δW| + |δW′|`；補集不變 `δ(Wᶜ) = δW`（`cutEdges_compl`）。
  證法：把邊數寫成逐邊指示函數的和（`card_cutEdges_eq_sum`），逐邊 16 種情形 `decide`。
  這是上界函數的不等式，**推不出** von Neumann 熵的強次可加性。
* **G5 最小割的 MMI**（`minCut_mmi`）：邊界頂點集 `bd`，對 `X ⊆ bd`，
  `minCut ends bd X` = 所有滿足 `W ∩ bd = X` 的 `W` 的割邊數的最小值（`minCut_le`、`exists_minCut`）。
  對兩兩不交的 `A B C ⊆ bd`：
  `mc(A) + mc(B) + mc(C) + mc(ABC) ≤ mc(AB) + mc(BC) + mc(AC)`。
  證法：取 `W_AB`、`W_BC`、`W_AC` 各達最小，逐頂點用三位元 `(v∈W_AB, v∈W_BC, v∈W_AC)` 的收縮映射
  `y_A = x_AB ∧ x_AC ∧ ¬x_BC`、`y_B = x_AB ∧ x_BC ∧ ¬x_AC`、`y_C = x_BC ∧ x_AC ∧ ¬x_AB`、
  `y_ABC = x_AB ∨ x_BC ∨ x_AC` 定出 `W_A`、`W_B`、`W_C`、`W_ABC`（`contractSet`）。
  它對 64 對三位元都滿足逐邊不等式（`mmi_contract`，`decide`），
  而且邊界條件正確（`mmi_boundary`：`W_A ∩ bd = A` 等）。
  四個邊界點的像被邊界條件固定後，其餘四個輸入的 16⁴ 種取值中只有這一組可行
  （Python 窮舉；唯一性沒有在 Lean 證）。
* **GHZ 違反 MMI**（`ghz4_mmi_fails`）：四方 GHZ 態 `(|0000⟩ + |1111⟩)/√2`（`ghz`）的
  任意單方、兩方、三方約化態都是 `diag(1/2, 1/2, 0, …)`（`regionState_ghz`），熵 = log 2
  （`regionEntropy_ghz`）。所以 `S(AB) + S(BC) + S(AC) = 3 log 2 < 4 log 2 = S(A) + S(B) + S(C) + S(ABC)`。
  * 約化態的定義（`regionState`）：純態按 `W | Wᶜ` 重排成矩陣 `Ψ`（`TensorNetwork.lean` 的 `cutMat`），
    約化態 `Ψ Ψᴴ`。它就是整個純態 `|ψ⟩⟨ψ|` 重新分組之後的 `ptrB`（`regionState_eq_ptrB_reindex`），
    所以七個熵都來自**同一個態**。
  * 推論（`ghz4_not_minCut`）：不存在任何圖、任何邊界、任何比例常數 `κ`，
    使 `κ · minCut` 在七個區域上重現 GHZ 的熵。
  圖可實現的熵（min-cut）滿足 MMI，量子熵不滿足；所以圖可實現的熵嚴格小於量子熵。
  這是幾何對態的最小可證約束；**不是** RT。
* **G1**（`rank_le_one_iff_vecMulVec`）：秩 ≤ 1 ⇔ 是一個外積 `vecMulVec u v`（mathlib 只有 ⇐）。
* **G2 割邊 0 ⇒ 乘積**（`tnAmp_product_of_no_cut`）：沒有割邊時，振幅分解成
  「`W` 上的函數 × `Wᶜ` 上的函數」。由 `rank_cutMat_tnAmp_le` 取 `D⁰ = 1` 再套 G1。
  * 負控制（`negctrl_product_with_bond`）：同一張圖、同一個割（有一條真的鍵，割邊數 1），
    頂點張量秩 1（`T_v(s, b) = f_v(s) g_v(b)`）時振幅仍是乘積（秩 ≤ 1）；Bell 張量則秩 2。
    所以「連通 ⇒ 糾纏」為假：秩 ≤ D^{割邊數} 只是上界。
* **G4 等號判準**（`rank_cutMat_eq_of_inj_surj`）：`cutLeft` 單射、`cutRight` 滿射 ⇒ 秩 = `D^{割邊數}`。

範圍（引用前請讀）：
* `minCut` 是組合定義（對 `Finset` 取最小），沒有 max-flow／Menger，也沒有連到極小曲面。
* MMI 是 min-cut 函數的性質；它說的是「哪些熵向量**不能**由圖的割重現」，不是任何態滿足的不等式。
* GHZ 那一段只談有限維矩陣的熵；「全像態必須滿足 MMI」（Hayden–Headrick–Maloney）的物理前提沒有形式化。
-/

namespace ErEpr

open Matrix

noncomputable section

variable {V E : Type*}

/-! ## 割邊數寫成逐邊指示函數的和 -/

/-- 割指示函數：兩個端點不在同一側時為 1。 -/
def cutInd (p q : Bool) : ℕ := if p = q then 0 else 1

theorem card_cutEdges_eq_sum [DecidableEq V] [Fintype E] (ends : E → V × V) (W : Finset V) :
    (cutEdges ends W).card =
      ∑ e, cutInd (decide ((ends e).1 ∈ W)) (decide ((ends e).2 ∈ W)) := by
  rw [cutEdges, Finset.card_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : (ends e).1 ∈ W <;> by_cases h2 : (ends e).2 ∈ W <;> simp [IsCut, cutInd, h1, h2]

/-! ## G6：次模性 -/

theorem cutInd_submod (a a' b b' : Bool) :
    cutInd (a || a') (b || b') + cutInd (a && a') (b && b') ≤ cutInd a b + cutInd a' b' := by
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- **G6 割函數的次模性**：`|δ(W ∪ W′)| + |δ(W ∩ W′)| ≤ |δW| + |δW′|`。 -/
theorem cutEdges_card_submodular [DecidableEq V] [Fintype E] (ends : E → V × V)
    (W W' : Finset V) :
    (cutEdges ends (W ∪ W')).card + (cutEdges ends (W ∩ W')).card ≤
      (cutEdges ends W).card + (cutEdges ends W').card := by
  simp only [card_cutEdges_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  simp only [Finset.mem_union, Finset.mem_inter, Bool.decide_or, Bool.decide_and]
  exact cutInd_submod _ _ _ _

/-- **G6** 補集的割邊與原集合相同。 -/
theorem cutEdges_compl [Fintype V] [DecidableEq V] [Fintype E] (ends : E → V × V)
    (W : Finset V) : cutEdges ends Wᶜ = cutEdges ends W := by
  ext e
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, IsCut, Finset.mem_compl,
    not_iff_not]

/-! ## G5：最小割 -/

/-- 邊界 `bd` 上的區域 `X` 的最小割：所有 `W ∩ bd = X` 的 `W` 中，割邊數的最小值。
（`X ⊄ bd` 時集合為空，`sInf ∅ = 0`；所有定理都假設 `X ⊆ bd`。） -/
def minCut [DecidableEq V] [Fintype E] (ends : E → V × V) (bd X : Finset V) : ℕ :=
  sInf {n | ∃ W : Finset V, W ∩ bd = X ∧ (cutEdges ends W).card = n}

/-- 保真：最小割不超過任何合格的割。 -/
theorem minCut_le [DecidableEq V] [Fintype E] (ends : E → V × V) {bd X W : Finset V}
    (hW : W ∩ bd = X) : minCut ends bd X ≤ (cutEdges ends W).card :=
  Nat.sInf_le ⟨W, hW, rfl⟩

/-- 保真：`X ⊆ bd` 時最小割達得到。 -/
theorem exists_minCut [DecidableEq V] [Fintype E] (ends : E → V × V) {bd X : Finset V}
    (hX : X ⊆ bd) : ∃ W : Finset V, W ∩ bd = X ∧ (cutEdges ends W).card = minCut ends bd X := by
  have hne : {n | ∃ W : Finset V, W ∩ bd = X ∧ (cutEdges ends W).card = n}.Nonempty :=
    ⟨_, X, Finset.inter_eq_left.mpr hX, rfl⟩
  obtain ⟨W, hW, h⟩ := Nat.sInf_mem hne
  exact ⟨W, hW, h⟩

/-- MMI 收縮映射的四個分量（輸入 `x = v∈W_AB`、`y = v∈W_BC`、`z = v∈W_AC`）。 -/
def mmiA (x y z : Bool) : Bool := x && z && !y
def mmiB (x y z : Bool) : Bool := x && y && !z
def mmiC (x y z : Bool) : Bool := y && z && !x
def mmiABC (x y z : Bool) : Bool := x || y || z

/-- **收縮性**：對 64 對三位元，四個輸出的漢明距離不超過三個輸入的漢明距離。 -/
theorem mmi_contract (x y z x' y' z' : Bool) :
    cutInd (mmiA x y z) (mmiA x' y' z') + cutInd (mmiB x y z) (mmiB x' y' z') +
        cutInd (mmiC x y z) (mmiC x' y' z') + cutInd (mmiABC x y z) (mmiABC x' y' z') ≤
      cutInd x x' + cutInd y y' + cutInd z z' := by
  cases x <;> cases y <;> cases z <;> cases x' <;> cases y' <;> cases z' <;> decide

/-- **邊界條件**：`A`、`B`、`C` 兩兩不交時，邊界頂點的三位元 `(a∨b, b∨c, a∨c)` 映到 `(a, b, c, a∨b∨c)`。 -/
theorem mmi_boundary (a b c : Bool) (hab : (a && b) = false) (hbc : (b && c) = false)
    (hac : (a && c) = false) :
    mmiA (a || b) (b || c) (a || c) = a ∧ mmiB (a || b) (b || c) (a || c) = b ∧
      mmiC (a || b) (b || c) (a || c) = c ∧ mmiABC (a || b) (b || c) (a || c) = (a || b || c) := by
  revert hab hbc hac
  cases a <;> cases b <;> cases c <;> decide

/-- 用收縮映射逐頂點定出的新頂點集。 -/
def contractSet [Fintype V] [DecidableEq V] (g : Bool → Bool → Bool → Bool)
    (W₁ W₂ W₃ : Finset V) : Finset V :=
  Finset.univ.filter fun v => g (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = true

theorem decide_mem_contractSet [Fintype V] [DecidableEq V] (g : Bool → Bool → Bool → Bool)
    (W₁ W₂ W₃ : Finset V) (v : V) :
    decide (v ∈ contractSet g W₁ W₂ W₃) = g (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) := by
  simp [contractSet]

theorem contractSet_inter [Fintype V] [DecidableEq V] {g : Bool → Bool → Bool → Bool}
    {W₁ W₂ W₃ bd X : Finset V}
    (h : ∀ v ∈ bd, g (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = decide (v ∈ X))
    (hX : X ⊆ bd) : contractSet g W₁ W₂ W₃ ∩ bd = X := by
  ext v
  rw [Finset.mem_inter]
  by_cases hv : v ∈ bd
  · rw [and_iff_left hv, ← decide_eq_decide, decide_mem_contractSet, h v hv]
  · exact ⟨fun h' => absurd h'.2 hv, fun h' => absurd (hX h') hv⟩

/-- 邊界上的頂點，`v ∈ W` 由 `W ∩ bd = X` 決定。 -/
theorem decide_mem_of_inter [DecidableEq V] {W bd X : Finset V} (h : W ∩ bd = X) {v : V}
    (hv : v ∈ bd) : decide (v ∈ W) = decide (v ∈ X) := by
  have := Finset.ext_iff.mp h v
  rw [Finset.mem_inter, and_iff_left hv] at this
  exact decide_eq_decide.mpr this

theorem decide_and_eq_false_of_disjoint [DecidableEq V] {A B : Finset V} (h : Disjoint A B)
    (v : V) : (decide (v ∈ A) && decide (v ∈ B)) = false := by
  rw [← Bool.decide_and]
  exact decide_eq_false fun hv => Finset.disjoint_left.mp h hv.1 hv.2

/-- **G5 最小割的 MMI**（monogamy of mutual information）：對兩兩不交的 `A B C ⊆ bd`，
`mc(A) + mc(B) + mc(C) + mc(ABC) ≤ mc(AB) + mc(BC) + mc(AC)`。 -/
theorem minCut_mmi [Fintype V] [DecidableEq V] [Fintype E] (ends : E → V × V)
    {bd A B C : Finset V} (hA : A ⊆ bd) (hB : B ⊆ bd) (hC : C ⊆ bd) (hAB : Disjoint A B)
    (hBC : Disjoint B C) (hAC : Disjoint A C) :
    minCut ends bd A + minCut ends bd B + minCut ends bd C + minCut ends bd (A ∪ B ∪ C) ≤
      minCut ends bd (A ∪ B) + minCut ends bd (B ∪ C) + minCut ends bd (A ∪ C) := by
  obtain ⟨W₁, h₁, e₁⟩ := exists_minCut ends (Finset.union_subset hA hB)
  obtain ⟨W₂, h₂, e₂⟩ := exists_minCut ends (Finset.union_subset hB hC)
  obtain ⟨W₃, h₃, e₃⟩ := exists_minCut ends (Finset.union_subset hA hC)
  have hx : ∀ v ∈ bd, decide (v ∈ W₁) = (decide (v ∈ A) || decide (v ∈ B)) ∧
      decide (v ∈ W₂) = (decide (v ∈ B) || decide (v ∈ C)) ∧
      decide (v ∈ W₃) = (decide (v ∈ A) || decide (v ∈ C)) := by
    intro v hv
    refine ⟨?_, ?_, ?_⟩
    · simp only [decide_mem_of_inter h₁ hv, Finset.mem_union, Bool.decide_or]
    · simp only [decide_mem_of_inter h₂ hv, Finset.mem_union, Bool.decide_or]
    · simp only [decide_mem_of_inter h₃ hv, Finset.mem_union, Bool.decide_or]
  have hbd : ∀ v ∈ bd,
      mmiA (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = decide (v ∈ A) ∧
      mmiB (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = decide (v ∈ B) ∧
      mmiC (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = decide (v ∈ C) ∧
      mmiABC (decide (v ∈ W₁)) (decide (v ∈ W₂)) (decide (v ∈ W₃)) = decide (v ∈ A ∪ B ∪ C) := by
    intro v hv
    obtain ⟨x1, x2, x3⟩ := hx v hv
    rw [x1, x2, x3]
    simp only [Finset.mem_union, Bool.decide_or]
    exact mmi_boundary _ _ _ (decide_and_eq_false_of_disjoint hAB v)
      (decide_and_eq_false_of_disjoint hBC v) (decide_and_eq_false_of_disjoint hAC v)
  have bA := contractSet_inter (g := mmiA) (fun v hv => (hbd v hv).1) hA
  have bB := contractSet_inter (g := mmiB) (fun v hv => (hbd v hv).2.1) hB
  have bC := contractSet_inter (g := mmiC) (fun v hv => (hbd v hv).2.2.1) hC
  have bABC := contractSet_inter (g := mmiABC) (fun v hv => (hbd v hv).2.2.2)
    (Finset.union_subset (Finset.union_subset hA hB) hC)
  have hsum : (cutEdges ends (contractSet mmiA W₁ W₂ W₃)).card +
      (cutEdges ends (contractSet mmiB W₁ W₂ W₃)).card +
      (cutEdges ends (contractSet mmiC W₁ W₂ W₃)).card +
      (cutEdges ends (contractSet mmiABC W₁ W₂ W₃)).card ≤
      (cutEdges ends W₁).card + (cutEdges ends W₂).card + (cutEdges ends W₃).card := by
    simp only [card_cutEdges_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    simp only [decide_mem_contractSet]
    exact mmi_contract _ _ _ _ _ _
  calc minCut ends bd A + minCut ends bd B + minCut ends bd C + minCut ends bd (A ∪ B ∪ C)
      ≤ (cutEdges ends (contractSet mmiA W₁ W₂ W₃)).card +
          (cutEdges ends (contractSet mmiB W₁ W₂ W₃)).card +
          (cutEdges ends (contractSet mmiC W₁ W₂ W₃)).card +
          (cutEdges ends (contractSet mmiABC W₁ W₂ W₃)).card :=
        add_le_add (add_le_add (add_le_add (minCut_le ends bA) (minCut_le ends bB))
          (minCut_le ends bC)) (minCut_le ends bABC)
    _ ≤ (cutEdges ends W₁).card + (cutEdges ends W₂).card + (cutEdges ends W₃).card := hsum
    _ = minCut ends bd (A ∪ B) + minCut ends bd (B ∪ C) + minCut ends bd (A ∪ C) := by
        rw [e₁, e₂, e₃]

/-! ## 區域的約化態 -/

/-- 區域 `W` 的約化態：純態 `ψ` 按 `W | Wᶜ` 重排成矩陣 `Ψ = cutMat W ψ`，約化態是 `Ψ Ψᴴ`。 -/
def regionState [Fintype V] [DecidableEq V] {σ : V → Type*} [∀ v, Fintype (σ v)]
    (W : Finset V) (ψ : ((v : V) → σ v) → ℂ) :
    Matrix ((v : {v // v ∈ W}) → σ v) ((v : {v // v ∈ W}) → σ v) ℂ :=
  cutMat W ψ * (cutMat W ψ)ᴴ

/-- 區域 `W` 的糾纏熵。 -/
def regionEntropy [Fintype V] [DecidableEq V] {σ : V → Type*} [∀ v, Fintype (σ v)]
    [∀ v, DecidableEq (σ v)] (W : Finset V) (ψ : ((v : V) → σ v) → ℂ) : ℝ :=
  vnEntropy (regionState W ψ)

/-- **保真**：`regionState` 就是整個純態 `|ψ⟩⟨ψ|` 按 `(W 上的指標, Wᶜ 上的指標)` 重新分組之後，
對 `Wᶜ` 取部分跡。所以各區域的熵都來自同一個態。 -/
theorem regionState_eq_ptrB_reindex [Fintype V] [DecidableEq V] {σ : V → Type*}
    [∀ v, Fintype (σ v)] (W : Finset V) (ψ : ((v : V) → σ v) → ℂ) :
    regionState W ψ = ptrB (reindex (Equiv.piEquivPiSubtypeProd (· ∈ W) σ)
      (Equiv.piEquivPiSubtypeProd (· ∈ W) σ) (vecMulVec ψ (star ψ))) := by
  rw [regionState, ← ptrB_pure]
  refine congrArg ptrB ?_
  ext i j
  rfl

/-- 熵在重新標號下不變。 -/
theorem vnEntropy_reindex {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (ρ : Matrix m m ℂ) : vnEntropy (reindex e e ρ) = vnEntropy ρ := by
  rw [vnEntropy, vnEntropy, charpoly_reindex]

/-! ## GHZ 態 -/

/-- `n` 方 GHZ 態的振幅 `(|0…0⟩ + |1…1⟩)/√2`。 -/
def ghz (n : ℕ) : (Fin n → Fin 2) → ℂ :=
  fun x => if x = (fun _ => 0) ∨ x = (fun _ => 1) then ((sBell : ℝ) : ℂ) else 0

theorem merge_eq_const {n : ℕ} {W : Finset (Fin n)} (y : {v // v ∈ W} → Fin 2)
    (z : {v // v ∉ W} → Fin 2) (c : Fin 2) :
    ((fun v => if h : v ∈ W then y ⟨v, h⟩ else z ⟨v, h⟩) = fun _ => c) ↔
      y = (fun _ => c) ∧ z = (fun _ => c) := by
  constructor
  · intro h
    refine ⟨funext fun v => ?_, funext fun v => ?_⟩
    · have := congrFun h v.1
      simpa [v.2] using this
    · have := congrFun h v.1
      simpa [v.2] using this
  · rintro ⟨rfl, rfl⟩
    funext v
    by_cases h : v ∈ W <;> simp [h]

theorem cutMat_ghz {n : ℕ} (W : Finset (Fin n)) (y : {v // v ∈ W} → Fin 2)
    (z : {v // v ∉ W} → Fin 2) :
    cutMat W (ghz n) y z =
      if (y = (fun _ => 0) ∧ z = (fun _ => 0)) ∨ (y = (fun _ => 1) ∧ z = (fun _ => 1))
      then ((sBell : ℝ) : ℂ) else 0 := by
  simp only [cutMat, of_apply, ghz, merge_eq_const]

theorem sBell_mul_star : ((sBell : ℝ) : ℂ) * star ((sBell : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, sBell_mul_self]
  norm_num

/-- 兩個點 `p ≠ q` 上各有振幅 `s`（`|s|² = 1/2`）時，`Ψ Ψᴴ` 的 `(y, y′)` 元。 -/
theorem two_point_entry {ι : Type*} [DecidableEq ι] {p q : ι} (hpq : p ≠ q) {s : ℂ}
    (hs : s * star s = 1 / 2) (y y' : ι) :
    (if y = p then s else 0) * star (if y' = p then s else 0) +
        (if y = q then s else 0) * star (if y' = q then s else 0) =
      if y = y' then (((if y = p ∨ y = q then 1 / 2 else 0 : ℝ)) : ℂ) else 0 := by
  by_cases hyy : y = y'
  · rw [← hyy, if_pos rfl]
    by_cases hp : y = p
    · rw [hp, if_pos rfl, if_neg hpq, if_pos (Or.inl rfl), star_zero, mul_zero, add_zero, hs]
      norm_num
    · by_cases hq : y = q
      · rw [hq, if_neg hpq.symm, if_pos rfl, if_pos (Or.inr rfl), star_zero, mul_zero, zero_add,
          hs]
        norm_num
      · rw [if_neg hp, if_neg hq, if_neg (not_or.mpr ⟨hp, hq⟩)]
        simp
  · rw [if_neg hyy]
    have h1 : ∀ r : ι, (if y = r then s else 0) * star (if y' = r then s else 0) = 0 := by
      intro r
      by_cases hr : y = r
      · have hr' : ¬y' = r := fun h => hyy (hr.trans h.symm)
        rw [if_neg hr', star_zero, mul_zero]
      · rw [if_neg hr, zero_mul]
    rw [h1 p, h1 q, add_zero]

/-- **GHZ 的約化態**：任何非空、非全體的區域 `W`，約化態都是 `diag(1/2, 1/2, 0, …)`
（只在全 0 與全 1 兩個指標上非零）。 -/
theorem regionState_ghz {n : ℕ} (W : Finset (Fin n)) (hW : ∃ v, v ∈ W) (hWc : ∃ v, v ∉ W) :
    regionState W (ghz n) =
      diagonal fun y => (((if y = (fun _ => 0) ∨ y = (fun _ => 1) then 1 / 2 else 0 : ℝ)) : ℂ) := by
  obtain ⟨a, ha⟩ := hW
  obtain ⟨b, hb⟩ := hWc
  have hy : (fun _ => 0 : {v // v ∈ W} → Fin 2) ≠ fun _ => 1 := fun h => by
    have := congrFun h ⟨a, ha⟩
    simp at this
  have hz : (fun _ => 0 : {v // v ∉ W} → Fin 2) ≠ fun _ => 1 := fun h => by
    have := congrFun h ⟨b, hb⟩
    simp at this
  have hc0 : ∀ y, cutMat W (ghz n) y (fun _ => 0) =
      if y = (fun _ => 0) then ((sBell : ℝ) : ℂ) else 0 := fun y => by
    rw [cutMat_ghz]
    simp [hz]
  have hc1 : ∀ y, cutMat W (ghz n) y (fun _ => 1) =
      if y = (fun _ => 1) then ((sBell : ℝ) : ℂ) else 0 := fun y => by
    rw [cutMat_ghz]
    simp [hz.symm]
  ext y y'
  rw [regionState, mul_apply, Fintype.sum_eq_add _ _ hz ?_]
  · rw [conjTranspose_apply, conjTranspose_apply, hc0, hc0, hc1, hc1, diagonal_apply]
    exact two_point_entry hy sBell_mul_star y y'
  · intro z hz'
    simp [conjTranspose_apply, cutMat_ghz, hz'.1, hz'.2]

/-- 對角元只在兩個點上是 1/2 的分布，熵是 log 2。 -/
theorem negMulLog_sum_two {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q) :
    ∑ y, Real.negMulLog (if y = p ∨ y = q then 1 / 2 else 0) = Real.log 2 := by
  rw [Fintype.sum_eq_add p q hpq fun y hy => by simp [hy.1, hy.2], if_pos (Or.inl rfl),
    if_pos (Or.inr rfl), Real.negMulLog, one_div, Real.log_inv]
  ring

/-- **GHZ 的區域熵**：任何非空、非全體的區域，熵都是 log 2。 -/
theorem regionEntropy_ghz {n : ℕ} (W : Finset (Fin n)) (hW : ∃ v, v ∈ W) (hWc : ∃ v, v ∉ W) :
    regionEntropy W (ghz n) = Real.log 2 := by
  have hy : (fun _ => 0 : {v // v ∈ W} → Fin 2) ≠ fun _ => 1 := fun h => by
    obtain ⟨a, ha⟩ := hW
    have := congrFun h ⟨a, ha⟩
    simp at this
  rw [regionEntropy, regionState_ghz W hW hWc, vnEntropy_diagonal]
  exact negMulLog_sum_two hy

/-- GHZ 的約化態確實歸一：跡為 1。 -/
theorem trace_regionState_ghz {n : ℕ} (W : Finset (Fin n)) (hW : ∃ v, v ∈ W)
    (hWc : ∃ v, v ∉ W) : trace (regionState W (ghz n)) = 1 := by
  have hy : (fun _ => 0 : {v // v ∈ W} → Fin 2) ≠ fun _ => 1 := fun h => by
    obtain ⟨a, ha⟩ := hW
    have := congrFun h ⟨a, ha⟩
    simp at this
  rw [regionState_ghz W hW hWc, trace_diagonal,
    Fintype.sum_eq_add _ _ hy fun y hy' => by simp [hy'.1, hy'.2], if_pos (Or.inl rfl),
    if_pos (Or.inr rfl), ← Complex.ofReal_add]
  norm_num

/-- **GHZ 違反 MMI**：四方 GHZ 態，`A = {0}`、`B = {1}`、`C = {2}`（第四方 `{3}` 是純化）：
`S(AB) + S(BC) + S(AC) = 3 log 2 < 4 log 2 = S(A) + S(B) + S(C) + S(ABC)`。
圖可實現的熵（min-cut）滿足 MMI（`minCut_mmi`），量子熵不滿足；
所以圖可實現的熵嚴格小於量子熵。這是幾何對態的最小可證約束；不是 RT。 -/
theorem ghz4_mmi_fails :
    regionEntropy ({0} ∪ {1} : Finset (Fin 4)) (ghz 4) +
        regionEntropy ({1} ∪ {2} : Finset (Fin 4)) (ghz 4) +
        regionEntropy ({0} ∪ {2} : Finset (Fin 4)) (ghz 4) <
      regionEntropy ({0} : Finset (Fin 4)) (ghz 4) + regionEntropy ({1} : Finset (Fin 4)) (ghz 4) +
        regionEntropy ({2} : Finset (Fin 4)) (ghz 4) +
        regionEntropy ({0} ∪ {1} ∪ {2} : Finset (Fin 4)) (ghz 4) := by
  rw [regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨1, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨1, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨2, by decide⟩ ⟨3, by decide⟩,
    regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩]
  linarith [Real.log_pos one_lt_two]

/-- **推論：GHZ 的熵不是任何圖的最小割**。對任何圖、任何邊界 `bd`、任何兩兩不交的 `A B C ⊆ bd`、
任何比例常數 `κ`（例如每條割邊 `log D`），`κ · minCut` 不可能在七個區域上都等於 GHZ 的熵。 -/
theorem ghz4_not_minCut [Fintype V] [DecidableEq V] [Fintype E] (ends : E → V × V)
    {bd A B C : Finset V} (hA : A ⊆ bd) (hB : B ⊆ bd) (hC : C ⊆ bd) (hAB : Disjoint A B)
    (hBC : Disjoint B C) (hAC : Disjoint A C) (κ : ℝ) :
    ¬ (κ * minCut ends bd A = regionEntropy ({0} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd B = regionEntropy ({1} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd C = regionEntropy ({2} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd (A ∪ B ∪ C) = regionEntropy ({0} ∪ {1} ∪ {2} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd (A ∪ B) = regionEntropy ({0} ∪ {1} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd (B ∪ C) = regionEntropy ({1} ∪ {2} : Finset (Fin 4)) (ghz 4) ∧
      κ * minCut ends bd (A ∪ C) = regionEntropy ({0} ∪ {2} : Finset (Fin 4)) (ghz 4)) := by
  rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rw [regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩] at h1
  rw [regionEntropy_ghz _ ⟨1, by decide⟩ ⟨3, by decide⟩] at h2
  rw [regionEntropy_ghz _ ⟨2, by decide⟩ ⟨3, by decide⟩] at h3
  rw [regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩] at h4
  rw [regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩] at h5
  rw [regionEntropy_ghz _ ⟨1, by decide⟩ ⟨3, by decide⟩] at h6
  rw [regionEntropy_ghz _ ⟨0, by decide⟩ ⟨3, by decide⟩] at h7
  have hl := Real.log_pos one_lt_two
  have hm : ((minCut ends bd A + minCut ends bd B + minCut ends bd C +
      minCut ends bd (A ∪ B ∪ C) : ℕ) : ℝ) ≤
      ((minCut ends bd (A ∪ B) + minCut ends bd (B ∪ C) + minCut ends bd (A ∪ C) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (minCut_mmi ends hA hB hC hAB hBC hAC)
  push_cast at hm
  have hκ : 0 < κ := by
    by_contra hk
    rw [not_lt] at hk
    have := mul_nonpos_of_nonpos_of_nonneg hk (Nat.cast_nonneg (minCut ends bd A))
    linarith
  have := mul_le_mul_of_nonneg_left hm hκ.le
  simp only [mul_add] at this
  linarith

/-! ## G1：秩 ≤ 1 ⇔ 外積 -/

/-- **G1** 秩 ≤ 1 若且唯若是一個外積 `vecMulVec u v`（mathlib 只有 ⇐：`rank_vecMulVec_le`）。 -/
theorem rank_le_one_iff_vecMulVec {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (Ψ : Matrix m n K) : Ψ.rank ≤ 1 ↔ ∃ u v, Ψ = vecMulVec u v := by
  classical
  constructor
  · intro h
    rw [Matrix.rank, finrank_le_one_iff] at h
    obtain ⟨w, hw⟩ := h
    choose c hc using fun j => hw ⟨Ψ.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
    refine ⟨(w : m → K), c, ?_⟩
    ext i j
    have := congrArg (fun x : LinearMap.range Ψ.mulVecLin => (x : m → K) i) (hc j)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
      mulVec_single_one, col_apply] at this
    rw [vecMulVec_apply, ← this, mul_comm]
  · rintro ⟨u, v, rfl⟩
    exact rank_vecMulVec_le u v

/-! ## G2：割邊 0 ⇒ 乘積 -/

variable {σ : V → Type*} {D : ℕ}

/-- **G2 割邊 0 ⇒ 乘積**：`W` 與 `Wᶜ` 之間沒有邊時，振幅分解成「`W` 上的函數 × `Wᶜ` 上的函數」。 -/
theorem tnAmp_product_of_no_cut [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (σ v)] (ends : E → V × V)
    (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) (W : Finset V)
    (h : (cutEdges ends W).card = 0) :
    ∃ (f : ((v : {v // v ∈ W}) → σ v) → ℂ) (g : ((v : {v // v ∉ W}) → σ v) → ℂ),
      ∀ x, tnAmp ends T x = f (fun v => x v) * g (fun v => x v) := by
  have hr := rank_cutMat_tnAmp_le ends T W
  rw [h, pow_zero] at hr
  obtain ⟨u, w, huw⟩ := (rank_le_one_iff_vecMulVec _).mp hr
  refine ⟨u, w, fun x => ?_⟩
  have := congrFun (congrFun huw (fun v => x v)) (fun v => x v)
  rw [vecMulVec_apply] at this
  rw [← this, cutMat, of_apply]
  congr 1
  funext v
  by_cases hv : v ∈ W <;> simp [hv]

/-- 頂點張量秩 1（`T_v(s, b) = f_v(s) g_v(b)`）時，振幅是物理指標的乘積乘上一個常數。 -/
theorem tnAmp_rankOne [Fintype V] [Fintype E] [DecidableEq E] (ends : E → V × V)
    (f : (v : V) → σ v → ℂ) (g : (v : V) → ({e : E // Inc ends v e} → Fin D) → ℂ)
    (x : (v : V) → σ v) :
    tnAmp ends (fun v s b => f v s * g v b) x =
      (∏ v, f v (x v)) * ∑ b : E → Fin D, ∏ v, g v fun e => b e.1 := by
  simp only [tnAmp, Finset.prod_mul_distrib, ← Finset.mul_sum]

/-- 頂點張量秩 1 時，任何割的切口矩陣秩 ≤ 1。 -/
theorem rank_cutMat_rankOne_le [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (σ v)] (ends : E → V × V) (f : (v : V) → σ v → ℂ)
    (g : (v : V) → ({e : E // Inc ends v e} → Fin D) → ℂ) (W : Finset V) :
    (cutMat W (tnAmp ends fun v s b => f v s * g v b)).rank ≤ 1 := by
  rw [rank_le_one_iff_vecMulVec]
  refine ⟨fun y => (∏ v : {v // v ∈ W}, f v (y v)) *
      ∑ b : E → Fin D, ∏ v, g v fun e => b e.1, fun z => ∏ v : {v // v ∉ W}, f v (z v), ?_⟩
  ext y z
  rw [cutMat, of_apply, tnAmp_rankOne, vecMulVec_apply,
    prod_split_mem W fun v => f v (if h : v ∈ W then y ⟨v, h⟩ else z ⟨v, h⟩)]
  have h1 : ∏ v : {v // v ∈ W}, f v (if h : (v : V) ∈ W then y ⟨v, h⟩ else z ⟨v, h⟩) =
      ∏ v : {v // v ∈ W}, f v (y v) :=
    Fintype.prod_congr _ _ fun v => by rw [dif_pos v.2]
  have h2 : ∏ v : {v // v ∉ W}, f v (if h : (v : V) ∈ W then y ⟨v, h⟩ else z ⟨v, h⟩) =
      ∏ v : {v // v ∉ W}, f v (z v) :=
    Fintype.prod_congr _ _ fun v => by rw [dif_neg v.2]
  rw [h1, h2]
  ring

/-! ## G4：等號判準 -/

/-- **G4 等號判準**：若割的左因子 `cutLeft`（作為線性映射）單射、右因子 `cutRight` 滿射，
切口秩恰為 `D^{割邊數}`：`rank_cutMat_tnAmp_le` 取等。
（負控制見 `negctrl_product_with_bond`：秩 1 的頂點張量讓單射失敗，秩掉到 1 < D。） -/
theorem rank_cutMat_eq_of_inj_surj [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (σ v)] (ends : E → V × V)
    (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) (W : Finset V)
    (hL : Function.Injective (cutLeft ends W T).mulVecLin)
    (hR : Function.Surjective (cutRight ends W T).mulVecLin) :
    (cutMat W (tnAmp ends T)).rank = D ^ (cutEdges ends W).card := by
  rw [cutMat_tnAmp, Matrix.rank, Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hR),
    LinearMap.finrank_range_of_inj hL, Module.finrank_fintype_fun_eq_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_subtype]
  rfl

/-- **G2 負控制：連通不推出糾纏**。兩格點路徑（一條真的鍵，割邊數 1、D = 2）上：
頂點張量秩 1 時切口秩 ≤ 1（乘積態），同一張圖、同一個割上 Bell 張量秩恰為 2。
所以 `rank_cutMat_tnAmp_le` 的 `D^{割邊數}` 只是上界，「有鍵 ⇒ 糾纏」為假。 -/
theorem negctrl_product_with_bond (f : (v : Fin 2) → Fin 2 → ℂ)
    (g : (v : Fin 2) → ({e : Unit // Inc path2Ends v e} → Fin 2) → ℂ) :
    (cutEdges path2Ends ({0} : Finset (Fin 2))).card = 1 ∧
      (cutMat ({0} : Finset (Fin 2)) (tnAmp path2Ends fun v s b => f v s * g v b)).rank ≤ 1 ∧
      (cutMat ({0} : Finset (Fin 2)) (tnAmp path2Ends bellTN)).rank = 2 :=
  ⟨card_cutEdges_path2, rank_cutMat_rankOne_le path2Ends f g _, rank_cutMat_bellTN⟩

end

end ErEpr
