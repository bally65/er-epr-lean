import ErEpr.Entropy

/-!
# ErEpr.TensorNetwork：一般圖張量網路的「∀ 割」秩上界

有限圖：頂點 `V`、邊 `E`，每條邊有兩個端點 `ends e : V × V`（可以相同，即自環）。
每條邊帶一個鍵指標 `Fin D`，每個頂點 `v` 帶一個物理指標 `σ v`（可以是 `Unit`，即沒有物理腳的內部頂點）。
頂點張量 `T v : σ v → (v 的入射邊 → Fin D) → ℂ`：**依型別**只看得見與 `v` 相連的邊上的鍵。
振幅 `ψ(x) = Σ_{b : E → Fin D} Π_v T_v(x_v; b|_{∂v})`（`tnAmp`）。

* **主定理** `rank_cutMat_tnAmp_le`：對任意頂點子集 `W`，把振幅重排成
  「`W` 上的物理指標 × `Wᶜ` 上的物理指標」的矩陣（`cutMat`），秩 ≤ `D ^ (割邊數)`；
  割邊＝恰有一端在 `W` 的邊（`cutEdges`）。
  證法：邊分成割邊／內邊（兩端都在 `W`）／外邊（兩端都不在 `W`），
  `W` 內的頂點只碰內邊與割邊，`Wᶜ` 內的頂點只碰外邊與割邊，所以矩陣分解成
  「左 × (割邊 → Fin D)」乘「(割邊 → Fin D) × 右」（`cutMat_tnAmp`）。
* **保真** `tnAmp_path2TN`：兩個頂點、一條邊的路徑上，這個一般振幅等於 `MPS.lean` 的開邊界 `mpsOpen`。
* **見證** `rank_cutMat_bellTN`：把 `MPS.lean` 的 Bell 對實例化成這個一般定義，
  割邊數 1（`card_cutEdges_path2`）、秩恰為 2 = D，上界是緊的。
* **保真＋見證（兩條割邊）** `tnAmp_ring2TN`、`rank_cutMat_ringBellTN`：兩格點的環（兩條平行邊）
  等於 `mpsRing`；`MPS.lean` 的環狀見證實例化後割邊數 2、秩恰為 4 = D²。
* **負控制** `negctrl_nonlocal_tensor`：若頂點張量可以看見非入射邊（`tnAmpAll`），上界就失敗：
  一條只接在頂點 0 上的自環（割邊數 0）就能讓頂點 1 也讀到它，造出秩 2 > 1 = D⁰。
  所以「依型別只看入射邊」是定理的實質內容。
* **面積律（熵版）** `cutEntropy_tnAmp_le`：歸一化之後，任一頂點子集 `W` 的糾纏熵
  ≤ 割邊數 × log D（S ≤ log 秩接上秩上界；一維特例是 `Entropy.lean` 的 T3a、T3b）。
  等號見證 `area_law_saturated`：`k` 條平行邊、任何 `k` 與 `D`，熵恰為 `k log D`（直接算成最大混合態，
  不經上界）。負控制 `negctrl_nonlocal_entropy`：上面那個非局域網路歸一之後，割邊數 0，熵卻是 log 2。

範圍（引用前請讀）：
* 這是 Ryu–Takayanagi 公式「≤」那一半的離散玩具版：秩（Rényi-0 熵 = log 秩）與 von Neumann 熵都只有上界。
  上界對任何圖、任何張量都成立，與全像無關；等號、最小割＝極小曲面、全像對偶都沒有證明，所以不稱 RT。
* `W` 是任意頂點子集，不必連通；「對所有分割取最小割」這一步沒有寫成定理。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder

noncomputable section

variable {V E : Type*} {σ : V → Type*} {D : ℕ}

/-! ## 定義 -/

/-- 邊 `e` 接在頂點 `v` 上：`v` 是 `e` 的一個端點。 -/
def Inc (ends : E → V × V) (v : V) (e : E) : Prop := (ends e).1 = v ∨ (ends e).2 = v

/-- 一般圖張量網路的振幅 `ψ(x) = Σ_b Π_v T_v(x_v; b|_{∂v})`。
頂點張量 `T v` 的鍵引數型別是「`v` 的入射邊 → `Fin D`」：依型別只看得見入射邊上的鍵。 -/
def tnAmp [Fintype V] [Fintype E] [DecidableEq E] (ends : E → V × V)
    (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) (x : (v : V) → σ v) : ℂ :=
  ∑ b : E → Fin D, ∏ v, T v (x v) fun e => b e.1

/-- 把頂點分成 `W` 與 `Wᶜ`，振幅重排成「`W` 上的物理指標 × `Wᶜ` 上的物理指標」的矩陣。
這個矩陣的秩就是該割的 Schmidt 秩。 -/
def cutMat [DecidableEq V] (W : Finset V) (ψ : ((v : V) → σ v) → ℂ) :
    Matrix ((v : {v // v ∈ W}) → σ v) ((v : {v // v ∉ W}) → σ v) ℂ :=
  Matrix.of fun y z => ψ fun v => if h : v ∈ W then y ⟨v, h⟩ else z ⟨v, h⟩

/-- 割邊：兩個端點不在 `W` 的同一側，即恰有一端在 `W`。 -/
def IsCut (ends : E → V × V) (W : Finset V) (e : E) : Prop :=
  ¬((ends e).1 ∈ W ↔ (ends e).2 ∈ W)

instance [DecidableEq V] (ends : E → V × V) (W : Finset V) : DecidablePred (IsCut ends W) :=
  fun e => inferInstanceAs (Decidable ¬((ends e).1 ∈ W ↔ (ends e).2 ∈ W))

/-- 內邊：兩個端點都在 `W`。 -/
def InW (ends : E → V × V) (W : Finset V) (e : E) : Prop := (ends e).1 ∈ W ∧ (ends e).2 ∈ W

instance [DecidableEq V] (ends : E → V × V) (W : Finset V) : DecidablePred (InW ends W) :=
  fun e => inferInstanceAs (Decidable ((ends e).1 ∈ W ∧ (ends e).2 ∈ W))

/-- 割邊的集合。 -/
def cutEdges [DecidableEq V] [Fintype E] (ends : E → V × V) (W : Finset V) : Finset E :=
  Finset.univ.filter (IsCut ends W)

/-! ## 局域性：頂點只碰得到哪些邊 -/

/-- `W` 內頂點的入射邊，若不是割邊，就是內邊。 -/
theorem inW_of_inc_mem {ends : E → V × V} {W : Finset V} {v : V} {e : E} (hv : v ∈ W)
    (he : Inc ends v e) (hc : ¬IsCut ends W e) : InW ends W e := by
  unfold IsCut at hc
  rw [not_not] at hc
  rcases he with h | h
  · have h1 : (ends e).1 ∈ W := h ▸ hv
    exact ⟨h1, hc.mp h1⟩
  · have h2 : (ends e).2 ∈ W := h ▸ hv
    exact ⟨hc.mpr h2, h2⟩

/-- `Wᶜ` 內頂點的入射邊不是內邊。 -/
theorem not_inW_of_inc_nmem {ends : E → V × V} {W : Finset V} {v : V} {e : E} (hv : v ∉ W)
    (he : Inc ends v e) : ¬InW ends W e := by
  rintro ⟨h1, h2⟩
  rcases he with h | h
  · exact hv (h ▸ h1)
  · exact hv (h ▸ h2)

/-! ## 分解：切口矩陣 = 左 × 右，內指標是割邊上的鍵 -/

/-- 割的左因子：`W` 內的頂點張量，對內邊上的鍵 `i` 求和；割邊上的鍵 `c` 是矩陣乘法的內指標。 -/
def cutLeft [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (ends : E → V × V)
    (W : Finset V) (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) :
    Matrix ((v : {v // v ∈ W}) → σ v) ({e // IsCut ends W e} → Fin D) ℂ :=
  Matrix.of fun y c => ∑ i : {x : {e // ¬IsCut ends W e} // InW ends W x.1} → Fin D,
    ∏ v : {v // v ∈ W}, T v (y v) fun e =>
      if h : IsCut ends W e.1 then c ⟨e.1, h⟩ else i ⟨⟨e.1, h⟩, inW_of_inc_mem v.2 e.2 h⟩

/-- 割的右因子：`Wᶜ` 內的頂點張量，對外邊上的鍵 `o` 求和。 -/
def cutRight [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (ends : E → V × V)
    (W : Finset V) (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) :
    Matrix ({e // IsCut ends W e} → Fin D) ((v : {v // v ∉ W}) → σ v) ℂ :=
  Matrix.of fun c z => ∑ o : {x : {e // ¬IsCut ends W e} // ¬InW ends W x.1} → Fin D,
    ∏ v : {v // v ∉ W}, T v (z v) fun e =>
      if h : IsCut ends W e.1 then c ⟨e.1, h⟩ else o ⟨⟨e.1, h⟩, not_inW_of_inc_nmem v.2 e.2⟩

/-- 對頂點的乘積拆成 `W` 與 `Wᶜ` 兩段。
（mathlib 的 `Fintype.prod_subtype_mul_prod_subtype` 用的是 `Subtype.fintype`，
這裡的 `{v // v ∈ W}` 用的是 `Finset.Subtype.fintype`；兩個 `Fintype` 實例由 `convert` 以子單元性對上。） -/
theorem prod_split_mem [Fintype V] [DecidableEq V] (W : Finset V) (f : V → ℂ) :
    ∏ v, f v = (∏ v : {v // v ∈ W}, f v) * ∏ v : {v // v ∉ W}, f v := by
  convert (Fintype.prod_subtype_mul_prod_subtype (· ∈ W) f).symm

/-- **分解**：任一割的切口矩陣 = 左因子 × 右因子，內指標是「割邊 → Fin D」。 -/
theorem cutMat_tnAmp [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → V × V) (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ)
    (W : Finset V) :
    cutMat W (tnAmp ends T) = cutLeft ends W T * cutRight ends W T := by
  ext y z
  rw [mul_apply]
  simp only [cutMat, tnAmp, cutLeft, cutRight, of_apply]
  rw [← (Equiv.piEquivPiSubtypeProd (IsCut ends W) fun _ => Fin D).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun c => ?_
  rw [Fintype.sum_mul_sum,
    ← (Equiv.piEquivPiSubtypeProd (fun x : {e // ¬IsCut ends W e} => InW ends W x.1)
      fun _ => Fin D).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun o => ?_
  rw [prod_split_mem W]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Fintype.prod_congr _ _ fun v => congrArg₂ (T v) (dif_pos v.2) (funext fun e => ?_)
    show (if h : IsCut ends W e.1 then c ⟨e.1, h⟩ else
        if h' : InW ends W e.1 then i ⟨⟨e.1, h⟩, h'⟩ else o ⟨⟨e.1, h⟩, h'⟩) = _
    by_cases h : IsCut ends W e.1
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, dif_pos (inW_of_inc_mem v.2 e.2 h)]
  · refine Fintype.prod_congr _ _ fun v => congrArg₂ (T v) (dif_neg v.2) (funext fun e => ?_)
    show (if h : IsCut ends W e.1 then c ⟨e.1, h⟩ else
        if h' : InW ends W e.1 then i ⟨⟨e.1, h⟩, h'⟩ else o ⟨⟨e.1, h⟩, h'⟩) = _
    by_cases h : IsCut ends W e.1
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, dif_neg (not_inW_of_inc_nmem v.2 e.2)]

/-! ## 主定理 -/

/-- **∀ 割秩上界**：一般圖張量網路，對任意頂點子集 `W`，切口矩陣的秩 ≤ `D ^ (割邊數)`。
割邊＝恰有一端在 `W` 的邊。（RT「≤」那一半的離散玩具版；不是 RT，見檔頭範圍。） -/
theorem rank_cutMat_tnAmp_le [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (σ v)] (ends : E → V × V)
    (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) (W : Finset V) :
    (cutMat W (tnAmp ends T)).rank ≤ D ^ (cutEdges ends W).card := by
  rw [cutMat_tnAmp]
  calc _ ≤ _ := rank_mul_le_left _ _
    _ ≤ Fintype.card ({e // IsCut ends W e} → Fin D) := rank_le_card_width _
    _ = D ^ (cutEdges ends W).card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype]
      rfl

/-! ## 保真：兩格點的路徑就是開邊界 MPS -/

/-- 兩個頂點 `0, 1`、一條邊連接它們的路徑。 -/
def path2Ends : Unit → Fin 2 × Fin 2 := fun _ => (0, 1)

/-- 路徑上唯一的那條邊，接在兩個頂點上。 -/
def path2Edge (v : Fin 2) : {e : Unit // Inc path2Ends v e} :=
  ⟨(), by fin_cases v <;> simp [Inc, path2Ends]⟩

/-- 兩格點開邊界 MPS `l · A₀(s₀) · A₁(s₁) · r` 寫成路徑上的頂點張量：
頂點 0 吸收左邊界 `l`，頂點 1 吸收右邊界 `r`，中間的鍵就是那條邊。 -/
def path2TN {τ : Type*} (l r : Fin D → ℂ) (A : Fin 2 → τ → Matrix (Fin D) (Fin D) ℂ) :
    (v : Fin 2) → τ → ({e : Unit // Inc path2Ends v e} → Fin D) → ℂ :=
  fun v s β => if v = 0 then (l ᵥ* A 0 s) (β (path2Edge v)) else (A 1 s *ᵥ r) (β (path2Edge v))

/-- 對 `Unit → Fin D` 求和就是對 `Fin D` 求和。 -/
theorem sum_unit_fun {M : Type*} [AddCommMonoid M] (F : (Unit → Fin D) → M) :
    ∑ b, F b = ∑ a : Fin D, F fun _ => a :=
  Fintype.sum_equiv (Equiv.funUnique Unit (Fin D)) _ _ fun _ => rfl

/-- **保真**：兩格點路徑上，一般圖張量網路的振幅就是開邊界 MPS 的振幅。 -/
theorem tnAmp_path2TN {τ : Type*} (l r : Fin D → ℂ) (A : Fin 2 → τ → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin 2 → τ) : tnAmp path2Ends (path2TN l r A) x = mpsOpen l r A x := by
  have hc : chainProd A x = A 0 (x 0) * A 1 (x 1) := by
    simp [chainProd, List.ofFn_succ]
  rw [mpsOpen, hc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, dotProduct, tnAmp,
    sum_unit_fun]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [Fin.prod_univ_two]
  simp [path2TN]

/-! ## 見證：Bell 對實例化成一般圖，上界是緊的 -/

/-- `MPS.lean` 的 Bell 對（`e0`、`bellA`，D = 2）實例化成一般圖張量網路。 -/
def bellTN : (v : Fin 2) → Fin 2 → ({e : Unit // Inc path2Ends v e} → Fin 2) → ℂ :=
  path2TN e0 e0 bellA

theorem tnAmp_bellTN (x : Fin 2 → Fin 2) :
    tnAmp path2Ends bellTN x = if x 0 = x 1 then 1 else 0 := by
  rw [bellTN, tnAmp_path2TN]
  exact mpsOpen_bell x

/-- 以 `W = {0}` 切開，唯一的邊是割邊。 -/
theorem card_cutEdges_path2 : (cutEdges path2Ends ({0} : Finset (Fin 2))).card = 1 := by
  decide

/-- **緊度見證**：Bell 對（D = 2）在一般圖定義下，割邊數 1、秩恰為 2 = D¹。 -/
theorem rank_cutMat_bellTN : (cutMat ({0} : Finset (Fin 2)) (tnAmp path2Ends bellTN)).rank = 2 := by
  apply le_antisymm
  · have h := rank_cutMat_tnAmp_le path2Ends bellTN ({0} : Finset (Fin 2))
    rwa [card_cutEdges_path2, pow_one] at h
  · have hsub : (cutMat ({0} : Finset (Fin 2)) (tnAmp path2Ends bellTN)).submatrix
        (fun a : Fin 2 => fun _ => a) (fun a : Fin 2 => fun _ => a) = 1 := by
      ext a b
      rw [submatrix_apply, cutMat, of_apply, tnAmp_bellTN, one_apply]
      simp
    have h := rank_submatrix_le (cutMat ({0} : Finset (Fin 2)) (tnAmp path2Ends bellTN))
      (fun a : Fin 2 => fun _ => a) (fun a : Fin 2 => fun _ => a)
    rwa [hsub, rank_one, Fintype.card_fin] at h

/-! ## 保真與見證：兩格點的環（兩條平行邊）就是環狀 MPS，割 2 條邊、秩恰為 D² -/

/-- 兩個頂點 `0, 1`、兩條平行邊（都連接 0 與 1）：兩格點的環。 -/
def ring2Ends : Fin 2 → Fin 2 × Fin 2 := fun _ => (0, 1)

/-- 環上的第 `j` 條邊，接在兩個頂點上。 -/
def ring2Edge (v j : Fin 2) : {e : Fin 2 // Inc ring2Ends v e} :=
  ⟨j, by fin_cases v <;> simp [Inc, ring2Ends]⟩

/-- 兩格點環狀 MPS `tr(A₀(s₀) A₁(s₁))` 寫成頂點張量：
邊 0 是 `A₀` 的列指標、`A₁` 的行指標；邊 1 是 `A₀` 的行指標、`A₁` 的列指標。 -/
def ring2TN {τ : Type*} (A : Fin 2 → τ → Matrix (Fin D) (Fin D) ℂ) :
    (v : Fin 2) → τ → ({e : Fin 2 // Inc ring2Ends v e} → Fin D) → ℂ :=
  fun v s β => if v = 0 then A 0 s (β (ring2Edge v 0)) (β (ring2Edge v 1))
    else A 1 s (β (ring2Edge v 1)) (β (ring2Edge v 0))

/-- **保真**：兩格點環上，一般圖張量網路的振幅就是環狀 MPS 的振幅。 -/
theorem tnAmp_ring2TN {τ : Type*} (A : Fin 2 → τ → Matrix (Fin D) (Fin D) ℂ) (x : Fin 2 → τ) :
    tnAmp ring2Ends (ring2TN A) x = mpsRing A x := by
  have hc : chainProd A x = A 0 (x 0) * A 1 (x 1) := by
    simp [chainProd, List.ofFn_succ]
  have hs : ∑ β : Fin 2 → Fin D, ∏ v, ring2TN A v (x v) (fun e => β e.1) =
      ∑ p : Fin D × Fin D, A 0 (x 0) p.1 p.2 * A 1 (x 1) p.2 p.1 :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin D) _ _ fun β => by
      simp [ring2TN, ring2Edge]
  rw [tnAmp, hs, Fintype.sum_prod_type, mpsRing, hc]
  simp [trace, mul_apply]

/-- `MPS.lean` 的環狀見證（`ringBellA`：兩條鍵各帶一個 Bell 對，D = 2）實例化成一般圖張量網路。 -/
def ringBellTN : (v : Fin 2) → Fin 2 × Fin 2 → ({e : Fin 2 // Inc ring2Ends v e} → Fin 2) → ℂ :=
  ring2TN ringBellA

theorem tnAmp_ringBellTN (x : Fin 2 → Fin 2 × Fin 2) :
    tnAmp ring2Ends ringBellTN x = if x 0 = x 1 then 1 else 0 := by
  rw [ringBellTN, tnAmp_ring2TN]
  exact mpsRing_ringBell x

/-- 以 `W = {0}` 切開，兩條邊都是割邊。 -/
theorem card_cutEdges_ring2 : (cutEdges ring2Ends ({0} : Finset (Fin 2))).card = 2 := by
  decide

/-- **緊度見證**：割 2 條邊時，秩恰為 4 = D²。所以主定理的指數確實是割邊數，不只對 1 條成立。 -/
theorem rank_cutMat_ringBellTN :
    (cutMat ({0} : Finset (Fin 2)) (tnAmp ring2Ends ringBellTN)).rank = 2 ^ 2 := by
  apply le_antisymm
  · have h := rank_cutMat_tnAmp_le ring2Ends ringBellTN ({0} : Finset (Fin 2))
    rwa [card_cutEdges_ring2] at h
  · have hsub : (cutMat ({0} : Finset (Fin 2)) (tnAmp ring2Ends ringBellTN)).submatrix
        (fun a : Fin 2 × Fin 2 => fun _ => a) (fun a : Fin 2 × Fin 2 => fun _ => a) = 1 := by
      ext a b
      rw [submatrix_apply, cutMat, of_apply, tnAmp_ringBellTN, one_apply]
      simp
    have h := rank_submatrix_le (cutMat ({0} : Finset (Fin 2)) (tnAmp ring2Ends ringBellTN))
      (fun a : Fin 2 × Fin 2 => fun _ => a) (fun a : Fin 2 × Fin 2 => fun _ => a)
    rw [hsub, rank_one] at h
    simpa using h

/-! ## 負控制：頂點張量若能看見非入射邊，上界就失敗 -/

/-- 不受限的振幅：每個頂點張量都看得見**所有**邊上的鍵。 -/
def tnAmpAll [Fintype V] [Fintype E] [DecidableEq E] (T : (v : V) → σ v → (E → Fin D) → ℂ)
    (x : (v : V) → σ v) : ℂ :=
  ∑ b : E → Fin D, ∏ v, T v (x v) b

/-- 兩個頂點、一條只接在頂點 0 上的自環。 -/
def loopEnds : Unit → Fin 2 × Fin 2 := fun _ => (0, 0)

/-- 以 `W = {0}` 切開，自環不是割邊：割邊數 0。 -/
theorem card_cutEdges_loop : (cutEdges loopEnds ({0} : Finset (Fin 2))).card = 0 := by
  decide

/-- 局域版本在這張圖上的上界：秩 ≤ 2⁰ = 1。 -/
theorem rank_cutMat_loop_le (T : (v : Fin 2) → Fin 2 → ({e : Unit // Inc loopEnds v e} → Fin 2) → ℂ) :
    (cutMat ({0} : Finset (Fin 2)) (tnAmp loopEnds T)).rank ≤ 1 := by
  have h := rank_cutMat_tnAmp_le loopEnds T ({0} : Finset (Fin 2))
  rwa [card_cutEdges_loop, pow_zero] at h

/-- 兩個頂點都讀自環上的鍵 `b`：`T_v(s; b) = [s = b]`。頂點 1 讀的是**非入射**邊。 -/
def loopT : (v : Fin 2) → Fin 2 → (Unit → Fin 2) → ℂ := fun _ s b => if s = b () then 1 else 0

theorem tnAmpAll_loopT (x : Fin 2 → Fin 2) : tnAmpAll loopT x = if x 0 = x 1 then 1 else 0 := by
  rw [tnAmpAll, sum_unit_fun, Fin.sum_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [loopT]
  generalize x 0 = p
  generalize x 1 = q
  fin_cases p <;> fin_cases q <;> simp

/-- **負控制**：讓頂點張量看得見非入射邊，同一張圖、同一個割（割邊數 0）上，秩是 2 > 1 = 2⁰。
所以 `rank_cutMat_tnAmp_le` 的內容來自「頂點張量依型別只看入射邊」。 -/
theorem negctrl_nonlocal_tensor :
    ¬ (cutMat ({0} : Finset (Fin 2)) (tnAmpAll loopT)).rank ≤
      2 ^ (cutEdges loopEnds ({0} : Finset (Fin 2))).card := by
  rw [card_cutEdges_loop, pow_zero, not_le]
  have hsub : (cutMat ({0} : Finset (Fin 2)) (tnAmpAll loopT)).submatrix
      (fun a : Fin 2 => fun _ => a) (fun a : Fin 2 => fun _ => a) = 1 := by
    ext a b
    rw [submatrix_apply, cutMat, of_apply, tnAmpAll_loopT, one_apply]
    simp
  have h := rank_submatrix_le (cutMat ({0} : Finset (Fin 2)) (tnAmpAll loopT))
    (fun a : Fin 2 => fun _ => a) (fun a : Fin 2 => fun _ => a)
  rw [hsub, rank_one, Fintype.card_fin] at h
  omega

/-! ## 面積律：熵版的 ∀ 割上界 -/

/-- 割 `W` 的糾纏熵：把振幅 `ψ` 當成純態 `|ψ⟩`（不另外歸一化），跡掉 `Wᶜ` 之後的 von Neumann 熵。 -/
def cutEntropy [Fintype V] [DecidableEq V] [∀ v, Fintype (σ v)] [∀ v, DecidableEq (σ v)]
    (W : Finset V) (ψ : ((v : V) → σ v) → ℂ) : ℝ :=
  vnEntropy (ptrB (vecMulVec (vecOf (cutMat W ψ)) (star (vecOf (cutMat W ψ)))))

/-- **面積律**：一般圖張量網路，歸一化之後，任一頂點子集 `W` 的糾纏熵 ≤ 割邊數 × log D。
證法：S ≤ log 秩（`vnEntropy_le_log_of_rank_le`）接上 ∀ 割秩上界（`rank_cutMat_tnAmp_le`）。
（RT「≤」那一半的離散玩具版；一維的特例是 `Entropy.lean` 的 `vnEntropy_cut_mpsOpen_le`、
`vnEntropy_cut_mpsRing_le`。） -/
theorem cutEntropy_tnAmp_le [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (σ v)] [∀ v, DecidableEq (σ v)] (ends : E → V × V)
    (T : (v : V) → σ v → ({e : E // Inc ends v e} → Fin D) → ℂ) (W : Finset V)
    (hnorm : trace (cutMat W (tnAmp ends T) * (cutMat W (tnAmp ends T))ᴴ) = 1) :
    cutEntropy W (tnAmp ends T) ≤ (cutEdges ends W).card * Real.log D := by
  rw [cutEntropy, ptrB_pure]
  have h := vnEntropy_le_log_of_rank_le (posSemidef_self_mul_conjTranspose _) hnorm
    (R := D ^ (cutEdges ends W).card)
    (by rw [rank_self_mul_conjTranspose]; exact rank_cutMat_tnAmp_le ends T W)
  rwa [Nat.cast_pow, Real.log_pow] at h

/-! ### 兩個頂點、振幅 `c·[x₀ = x₁]` 的割：熵恰為 log (物理維度) -/

/-- `W = {0}` 時，`W` 上的物理指標就是頂點 0 的物理指標。 -/
def evalZero (τ : Type*) : ((v : {v : Fin 2 // v ∈ ({0} : Finset (Fin 2))}) → τ) ≃ τ where
  toFun y := y ⟨0, Finset.mem_singleton_self 0⟩
  invFun a _ := a
  left_inv y := funext fun ⟨v, hv⟩ => by
    rw [Finset.mem_singleton] at hv
    subst hv
    rfl
  right_inv _ := rfl

/-- `W = {0}` 時，`Wᶜ` 上的物理指標就是頂點 1 的物理指標。 -/
def evalOne (τ : Type*) : ((v : {v : Fin 2 // v ∉ ({0} : Finset (Fin 2))}) → τ) ≃ τ where
  toFun z := z ⟨1, by simp⟩
  invFun a _ := a
  left_inv z := funext fun ⟨v, hv⟩ => by
    fin_cases v
    · simp at hv
    · rfl
  right_inv _ := rfl

variable {τ : Type*} [Fintype τ] [DecidableEq τ] {ψ : (Fin 2 → τ) → ℂ} {c : ℝ}

omit [Fintype τ] in
/-- 振幅 `ψ(x) = c·[x₀ = x₁]` 的切口矩陣是 `c` 乘上重排過的單位矩陣。 -/
theorem cutMat_diag (hψ : ∀ x, ψ x = (c : ℂ) * if x 0 = x 1 then 1 else 0) :
    cutMat (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ =
      (c : ℂ) • (1 : Matrix τ τ ℂ).submatrix (evalZero τ) (evalOne τ) := by
  ext y z
  rw [cutMat, of_apply, hψ]
  simp [evalZero, evalOne, one_apply]

theorem cutMat_diag_mul_conjTranspose (hψ : ∀ x, ψ x = (c : ℂ) * if x 0 = x 1 then 1 else 0)
    (hc : c * c = (Fintype.card τ : ℝ)⁻¹) :
    cutMat (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ *
        (cutMat (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ)ᴴ =
      (((Fintype.card τ : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
  rw [cutMat_diag hψ, conjTranspose_smul, conjTranspose_submatrix, conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, submatrix_mul_equiv, Matrix.one_mul, submatrix_one_equiv,
    smul_smul, ← hc]
  congr 1
  simp

/-- 歸一：`|c|² · dim τ = 1` 時 `tr(Ψ Ψᴴ) = 1`。 -/
theorem trace_cutMat_diag [Nonempty τ] (hψ : ∀ x, ψ x = (c : ℂ) * if x 0 = x 1 then 1 else 0)
    (hc : c * c = (Fintype.card τ : ℝ)⁻¹) :
    trace (cutMat (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ *
      (cutMat (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ)ᴴ) = 1 := by
  have h0 : (Fintype.card τ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [cutMat_diag_mul_conjTranspose hψ hc, trace_smul, trace_one, Fintype.card_congr (evalZero τ),
    smul_eq_mul]
  push_cast
  exact inv_mul_cancel₀ h0

/-- 熵恰為 `log (dim τ)`：約化態是 τ 上的最大混合態。 -/
theorem cutEntropy_diag [Nonempty τ] (hψ : ∀ x, ψ x = (c : ℂ) * if x 0 = x 1 then 1 else 0)
    (hc : c * c = (Fintype.card τ : ℝ)⁻¹) :
    cutEntropy (σ := fun _ => τ) ({0} : Finset (Fin 2)) ψ = Real.log (Fintype.card τ) := by
  rw [cutEntropy, ptrB_pure, cutMat_diag_mul_conjTranspose hψ hc,
    ← Fintype.card_congr (evalZero τ), vnEntropy_maxMixed]

/-! ### 緊度見證：k 條平行邊，熵恰為 k log D（任何 k、任何 D） -/

/-- 兩個頂點、`k` 條平行邊，每條都連接頂點 0 與 1。 -/
def parEnds (k : ℕ) : Fin k → Fin 2 × Fin 2 := fun _ => (0, 1)

/-- 每條平行邊都接在兩個頂點上。 -/
def parEdge (k : ℕ) (v : Fin 2) (e : Fin k) : {e' : Fin k // Inc (parEnds k) v e'} :=
  ⟨e, by fin_cases v <;> simp [Inc, parEnds]⟩

/-- 以 `W = {0}` 切開，`k` 條邊全是割邊。 -/
theorem card_cutEdges_par (k : ℕ) : (cutEdges (parEnds k) ({0} : Finset (Fin 2))).card = k := by
  have h : cutEdges (parEnds k) ({0} : Finset (Fin 2)) = Finset.univ := by
    ext e
    simp [cutEdges, IsCut, parEnds]
  rw [h, Finset.card_univ, Fintype.card_fin]

/-- 頂點張量：每個頂點有 `k` 隻物理腳，把它們複製到 `k` 條鍵上（`[s = β]`）；
頂點 0 另乘上歸一化係數 `c`。整個網路就是 `k` 對 D 維最大糾纏對。 -/
def parTN (k D : ℕ) (c : ℂ) :
    (v : Fin 2) → (Fin k → Fin D) → ({e : Fin k // Inc (parEnds k) v e} → Fin D) → ℂ :=
  fun v s β => (if v = 0 then c else 1) * if s = fun e => β (parEdge k v e) then 1 else 0

theorem tnAmp_parTN (k D : ℕ) (c : ℂ) (x : Fin 2 → Fin k → Fin D) :
    tnAmp (parEnds k) (parTN k D c) x = c * if x 0 = x 1 then 1 else 0 := by
  have h : ∀ b : Fin k → Fin D, ∏ v, parTN k D c v (x v) (fun e => b e.1) =
      c * ((if x 0 = b then 1 else 0) * if x 1 = b then 1 else 0) := by
    intro b
    rw [Fin.prod_univ_two]
    simp only [parTN]
    split_ifs <;> simp_all [parEdge]
  rw [tnAmp]
  simp_rw [h]
  rw [← Finset.mul_sum]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

/-- 歸一化係數 `1/√(D^k)`。 -/
def parC (k D : ℕ) : ℝ := (Real.sqrt ((D : ℝ) ^ k))⁻¹

theorem parC_mul_self (k D : ℕ) : parC k D * parC k D = ((D : ℝ) ^ k)⁻¹ := by
  rw [parC, ← mul_inv, Real.mul_self_sqrt (by positivity)]

/-- **面積律的等號達得到**：`k` 條平行邊、鍵維度 `D`（> 0），歸一之後割 `{0}` 的熵
恰好是 割邊數 × log D = k log D。所以 `cutEntropy_tnAmp_le` 的上界對每個割邊數都是緊的。
這裡的熵是直接算出來的（最大混合態），不經面積律本身。 -/
theorem area_law_saturated (k D : ℕ) (hD : 0 < D) :
    trace (cutMat ({0} : Finset (Fin 2)) (tnAmp (parEnds k) (parTN k D (parC k D))) *
        (cutMat ({0} : Finset (Fin 2)) (tnAmp (parEnds k) (parTN k D (parC k D))))ᴴ) = 1 ∧
      cutEntropy ({0} : Finset (Fin 2)) (tnAmp (parEnds k) (parTN k D (parC k D))) =
        (cutEdges (parEnds k) ({0} : Finset (Fin 2))).card * Real.log D := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hψ := tnAmp_parTN k D (parC k D)
  have hc : parC k D * parC k D = (Fintype.card (Fin k → Fin D) : ℝ)⁻¹ := by
    rw [parC_mul_self, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  refine ⟨trace_cutMat_diag (ψ := tnAmp (parEnds k) (parTN k D (parC k D))) hψ hc, ?_⟩
  rw [cutEntropy_diag (ψ := tnAmp (parEnds k) (parTN k D (parC k D))) hψ hc, card_cutEdges_par,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, Real.log_pow]

/-! ### 負控制：頂點張量看得見非入射邊時，面積律失敗 -/

/-- **負控制（熵版）**：`negctrl_nonlocal_tensor` 那個非局域網路，歸一化之後，
割邊數 0（上界是 0 · log 2 = 0），熵卻是 log 2 > 0。歸一化成立，所以失敗不是歸一化造成的。 -/
theorem negctrl_nonlocal_entropy :
    trace (cutMat (σ := fun _ => Fin 2) ({0} : Finset (Fin 2))
          (fun x => (sBell : ℂ) * tnAmpAll loopT x) *
        (cutMat (σ := fun _ => Fin 2) ({0} : Finset (Fin 2))
          (fun x => (sBell : ℂ) * tnAmpAll loopT x))ᴴ) = 1 ∧
      ¬ cutEntropy (σ := fun _ => Fin 2) ({0} : Finset (Fin 2))
          (fun x => (sBell : ℂ) * tnAmpAll loopT x) ≤
        (cutEdges loopEnds ({0} : Finset (Fin 2))).card * Real.log 2 := by
  have hψ : ∀ x : Fin 2 → Fin 2,
      (sBell : ℂ) * tnAmpAll loopT x = (sBell : ℂ) * if x 0 = x 1 then 1 else 0 := fun x => by
    rw [tnAmpAll_loopT]
  have hc : sBell * sBell = (Fintype.card (Fin 2) : ℝ)⁻¹ := by
    rw [sBell_mul_self, Fintype.card_fin]
    norm_num
  refine ⟨trace_cutMat_diag (ψ := fun x => (sBell : ℂ) * tnAmpAll loopT x) hψ hc, ?_⟩
  rw [cutEntropy_diag (ψ := fun x => (sBell : ℂ) * tnAmpAll loopT x) hψ hc, card_cutEdges_loop,
    Fintype.card_fin, Nat.cast_zero, zero_mul, not_le]
  exact Real.log_pos (by norm_num)

end

end ErEpr
