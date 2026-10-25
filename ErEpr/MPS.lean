import ErEpr.Basic

/-!
# ErEpr.MPS：T3 矩陣乘積態的秩上界

鍵維度 `D` 的矩陣乘積態（MPS）在一個切口處的 Schmidt 秩（把振幅重排成「左 × 右」矩陣後的秩），
不超過 `D` 的「割邊數」次方：
* 開邊界的鏈，任一處切開只割 1 條鍵：秩 ≤ D（`rank_cutAt_mpsOpen_le`）；
* 環狀（週期邊界）切成兩段連續區間要割 2 條鍵：秩 ≤ D²（`rank_cutAt_mpsRing_le`）；
* 上界是緊的：Bell 對（D = 2）的秩恰好是 2（`rank_cutAt_bell`）；
* 秩也就是該切口 A 側約化密度矩陣的秩（`rank_ptrB_pure`）。

範圍（引用前請讀）：
* 這是 Ryu–Takayanagi 公式「≤」那一半的離散玩具版，只談秩（Rényi-0 熵 = log 秩），
  還沒有 von Neumann 熵。
* 等號、最小割＝極小曲面、全像對偶都沒有證明；而且這個上界對任何 MPS 都成立，
  包括與全像無關的網路。所以這裡不稱 RT。

設計見 `DESIGN.md` §5。
-/

namespace ErEpr

open Matrix
open scoped ComplexOrder

noncomputable section

variable {σ : Type*} [Fintype σ] {D : ℕ}

/-! ## 定義 -/

/-- 沿鏈依序相乘：`A₁(x₁) A₂(x₂) ⋯ Aₙ(xₙ)`。 -/
def chainProd {n : ℕ} (A : Fin n → σ → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → σ) :
    Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i => A i (x i)).prod

/-- 開邊界 MPS 振幅 `ψ(x) = l · A₁(x₁) ⋯ Aₙ(xₙ) · r`。 -/
def mpsOpen {n : ℕ} (l r : Fin D → ℂ) (A : Fin n → σ → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → σ) : ℂ :=
  l ⬝ᵥ (chainProd A x *ᵥ r)

/-- 環狀（週期邊界）MPS 振幅 `ψ(x) = tr(A₁(x₁) ⋯ Aₙ(xₙ))`。 -/
def mpsRing {n : ℕ} (A : Fin n → σ → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → σ) : ℂ :=
  trace (chainProd A x)

/-- 把 `k + m` 個格點上的振幅在第 `k` 個格點之後切開，重排成「左 `k` 格 × 右 `m` 格」的矩陣。
這個矩陣的秩就是該切口的 Schmidt 秩。 -/
def cutAt (k m : ℕ) (ψ : (Fin (k + m) → σ) → ℂ) : Matrix (Fin k → σ) (Fin m → σ) ℂ :=
  Matrix.of fun y z => ψ (Fin.append y z)

/-! ## 鏈在切口處分成兩段 -/

omit [Fintype σ] in
theorem chainProd_append {k m : ℕ} (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ)
    (y : Fin k → σ) (z : Fin m → σ) :
    chainProd A (Fin.append y z) =
      chainProd (fun i => A (Fin.castLE (Nat.le_add_right k m) i)) y *
        chainProd (fun j => A (Fin.natAdd k j)) z := by
  simp only [chainProd]
  rw [List.ofFn_add, List.prod_append]
  simp [Fin.append_left', Fin.append_right]

/-! ## T3a：開邊界 -/

omit [Fintype σ] in
/-- 開邊界 MPS 的切口矩陣分解成「左 × D」乘「D × 右」。 -/
theorem cutAt_mpsOpen {k m : ℕ} (l r : Fin D → ℂ)
    (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    cutAt k m (mpsOpen l r A) =
      (Matrix.of fun (y : Fin k → σ) (a : Fin D) =>
          (l ᵥ* chainProd (fun i => A (Fin.castLE (Nat.le_add_right k m) i)) y) a) *
        (Matrix.of fun (a : Fin D) (z : Fin m → σ) =>
          (chainProd (fun j => A (Fin.natAdd k j)) z *ᵥ r) a) := by
  ext y z
  simp only [cutAt, mpsOpen, of_apply, mul_apply, chainProd_append]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rfl

/-- **T3a**：開邊界 MPS 在任一處切開，Schmidt 秩 ≤ D（割 1 條鍵）。 -/
theorem rank_cutAt_mpsOpen_le {k m : ℕ} (l r : Fin D → ℂ)
    (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    (cutAt k m (mpsOpen l r A)).rank ≤ D := by
  rw [cutAt_mpsOpen]
  calc _ ≤ _ := rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin D) := rank_le_card_width _
    _ = D := Fintype.card_fin D

/-! ## T3b：環狀 -/

omit [Fintype σ] in
/-- 環狀 MPS 的切口矩陣分解成「左 × (D × D)」乘「(D × D) × 右」：兩條鍵各貢獻一個指標。 -/
theorem cutAt_mpsRing {k m : ℕ} (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    cutAt k m (mpsRing A) =
      (Matrix.of fun (y : Fin k → σ) (p : Fin D × Fin D) =>
          chainProd (fun i => A (Fin.castLE (Nat.le_add_right k m) i)) y p.1 p.2) *
        (Matrix.of fun (p : Fin D × Fin D) (z : Fin m → σ) =>
          chainProd (fun j => A (Fin.natAdd k j)) z p.2 p.1) := by
  ext y z
  simp only [cutAt, mpsRing, of_apply, mul_apply, chainProd_append, trace, diag_apply,
    Fintype.sum_prod_type]

/-- **T3b**：環狀 MPS 切成兩段連續區間，Schmidt 秩 ≤ D²（割 2 條鍵）。 -/
theorem rank_cutAt_mpsRing_le {k m : ℕ} (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    (cutAt k m (mpsRing A)).rank ≤ D ^ 2 := by
  rw [cutAt_mpsRing]
  calc _ ≤ _ := rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin D × Fin D) := rank_le_card_width _
    _ = D ^ 2 := by simp [sq]

/-! ## 秩＝約化密度矩陣的秩 -/

/-- 純態 `|vec Ψ⟩` 的 A 側約化密度矩陣，秩等於 `Ψ` 的秩（Schmidt 秩）。 -/
theorem rank_ptrB_pure {ι κ : Type*} [Fintype ι] [Fintype κ] (Ψ : Matrix ι κ ℂ) :
    (ptrB (vecMulVec (vecOf Ψ) (star (vecOf Ψ)))).rank = Ψ.rank := by
  rw [ptrB_pure, rank_self_mul_conjTranspose]

/-- 開邊界 MPS 在切口處的 A 側約化密度矩陣，秩 ≤ D。 -/
theorem rank_ptrB_mpsOpen_le {k m : ℕ} (l r : Fin D → ℂ)
    (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    (ptrB (vecMulVec (vecOf (cutAt k m (mpsOpen l r A)))
      (star (vecOf (cutAt k m (mpsOpen l r A)))))).rank ≤ D := by
  rw [rank_ptrB_pure]
  exact rank_cutAt_mpsOpen_le l r A

/-! ## 緊度見證：Bell 對 -/

/-- Bell 對的 MPS：兩個格點、D = 2；`A₀(s) = |0⟩⟨s|`、`A₁(s) = |s⟩⟨0|`。 -/
def bellA : Fin (1 + 1) → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i s => if i = 0 then single 0 s 1 else single s 0 1

/-- 邊界向量 `e₀`。 -/
def e0 : Fin 2 → ℂ := Pi.single 0 1

/-- Bell 對的振幅：`ψ(x₀, x₁) = [x₀ = x₁]`，即 `|00⟩ + |11⟩`（未歸一化）。 -/
theorem mpsOpen_bell (x : Fin (1 + 1) → Fin 2) :
    mpsOpen e0 e0 bellA x = if x 0 = x 1 then 1 else 0 := by
  simp [mpsOpen, chainProd, bellA, e0, List.ofFn_succ, mulVec, dotProduct, mul_apply,
    single_apply, Fin.sum_univ_two]
  generalize x 0 = a
  generalize x 1 = b
  fin_cases a <;> fin_cases b <;> simp

/-- Bell 對在中間切開，切口矩陣是單位矩陣。 -/
theorem cutAt_bell : cutAt 1 1 (mpsOpen e0 e0 bellA) = 1 := by
  ext y z
  have h0 : Fin.append y z 0 = y 0 := rfl
  have h1 : Fin.append y z 1 = z 0 := rfl
  have hyz : y = z ↔ y 0 = z 0 :=
    ⟨fun h => h ▸ rfl, fun h => funext fun i => by fin_cases i; exact h⟩
  rw [cutAt, of_apply, mpsOpen_bell, h0, h1, one_apply]
  simp only [hyz]

/-- **緊度見證**：Bell 對（D = 2）的 Schmidt 秩恰好是 2，T3a 的上界達得到。 -/
theorem rank_cutAt_bell : (cutAt 1 1 (mpsOpen e0 e0 bellA)).rank = 2 := by
  rw [cutAt_bell, rank_one]
  simp

/-! ## 緊度見證：環狀 MPS 的秩恰為 D² -/

/-- 環狀 MPS 的緊度見證：兩個格點、D = 2、物理指標 `s = (a, b) ∈ Fin 2 × Fin 2`；
`A₀(a,b) = |a⟩⟨b|`、`A₁(c,d) = |d⟩⟨c|`。兩條鍵各帶一個 Bell 對。 -/
def ringBellA : Fin (1 + 1) → (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i s => if i = 0 then single s.1 s.2 1 else single s.2 s.1 1

/-- 振幅：`ψ(x₀, x₁) = [x₀ = x₁]`。 -/
theorem mpsRing_ringBell (x : Fin (1 + 1) → Fin 2 × Fin 2) :
    mpsRing ringBellA x = if x 0 = x 1 then 1 else 0 := by
  simp [mpsRing, chainProd, ringBellA, List.ofFn_succ, trace, mul_apply, single_apply,
    Fin.sum_univ_two]
  generalize x 0 = p
  generalize x 1 = q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp

/-- 切口矩陣是單位矩陣。 -/
theorem cutAt_ringBell : cutAt 1 1 (mpsRing ringBellA) = 1 := by
  ext y z
  have h0 : Fin.append y z 0 = y 0 := rfl
  have h1 : Fin.append y z 1 = z 0 := rfl
  have hyz : y = z ↔ y 0 = z 0 :=
    ⟨fun h => h ▸ rfl, fun h => funext fun i => by fin_cases i; exact h⟩
  rw [cutAt, of_apply, mpsRing_ringBell, h0, h1, one_apply]
  simp only [hyz]

/-- **緊度見證**：這個環狀 MPS（D = 2）的 Schmidt 秩恰好是 4 = D²，T3b 的上界達得到。 -/
theorem rank_cutAt_ringBell : (cutAt 1 1 (mpsRing ringBellA)).rank = 2 ^ 2 := by
  rw [cutAt_ringBell, rank_one]
  simp

end

end ErEpr
