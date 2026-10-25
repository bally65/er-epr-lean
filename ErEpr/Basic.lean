import Mathlib

/-!
# ErEpr.Basic：部分跡、區塊與 `id ⊗ Φ`

ER=EPR 字典中 EPR 側玩具零件的定義層。全部是有限維複矩陣上的定義與引理；
物理名詞只出現在註解，定理只談矩陣。設計見 `DESIGN.md` §2（保真引理 F1–F8）。

慣例：`Matrix (ι × κ) (ι × κ) ℂ` 的左因子是 A（`ι`），右因子是 B（`κ`）。
`ptrB` 對 B 取跡、保留 A；`ptrA` 對 A 取跡、保留 B。
-/

namespace ErEpr

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι κ κ' : Type*}

/-! ## 定義 -/

/-- 對右因子 B 取跡，保留左因子 A。 -/
def ptrB [Fintype κ] (X : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ k, X (i, k) (j, k)

@[simp] theorem ptrB_apply [Fintype κ] (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    ptrB X i j = ∑ k, X (i, k) (j, k) := rfl

/-- 對左因子 A 取跡，保留右因子 B：先用 `Prod.swap` 重排，再套 `ptrB`。 -/
def ptrA [Fintype ι] (X : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  ptrB (X.submatrix Prod.swap Prod.swap)

@[simp] theorem ptrA_apply [Fintype ι] (X : Matrix (ι × κ) (ι × κ) ℂ) (k l : κ) :
    ptrA X k l = ∑ i, X (i, k) (i, l) := rfl

/-- 第 `(i, j)` 個 `κ × κ` 區塊。 -/
def blk (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) : Matrix κ κ ℂ :=
  Matrix.of fun k l => X (i, k) (j, l)

@[simp] theorem blk_apply (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) (k l : κ) :
    blk X i j k l = X (i, k) (j, l) := rfl

theorem blk_add (X Y : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    blk (X + Y) i j = blk X i j + blk Y i j := by
  ext k l; simp

theorem blk_smul (c : ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    blk (c • X) i j = c • blk X i j := by
  ext k l; simp

/-- `id ⊗ Φ`：在每個 `(i, j)` 區塊上套 `Φ`。
它真的是 `id ⊗ Φ`，由 `idKron_kronecker`（F7）與 `idKron_unique`（F8）保證。 -/
def idKron (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × κ') (ι × κ') ℂ where
  toFun X := Matrix.of fun p q => Φ (blk X p.1 q.1) p.2 q.2
  map_add' X Y := by ext p q; simp [blk_add]
  map_smul' c X := by ext p q; simp [blk_smul]

@[simp] theorem idKron_apply (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (X : Matrix (ι × κ) (ι × κ) ℂ) (p q : ι × κ') :
    idKron Φ X p q = Φ (blk X p.1 q.1) p.2 q.2 := rfl

/-- `id ⊗ Φ` 之後再對 B 取跡：每個元素是一個區塊經 `Φ` 之後的跡。 -/
theorem ptrB_idKron_apply [Fintype κ'] (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) :
    ptrB (idKron Φ X) i j = trace (Φ (blk X i j)) := by
  simp [trace]

/-- 把矩陣 `S` 攤平成 `ι × κ` 上的向量：`vec S = Σ S_ik |i⟩|k⟩`。 -/
def vecOf (S : Matrix ι κ ℂ) : ι × κ → ℂ := fun p => S p.1 p.2

@[simp] theorem vecOf_apply (S : Matrix ι κ ℂ) (i : ι) (k : κ) :
    vecOf S (i, k) = S i k := rfl

/-! ## 部分跡的線性 -/

theorem ptrB_add [Fintype κ] (X Y : Matrix (ι × κ) (ι × κ) ℂ) : ptrB (X + Y) = ptrB X + ptrB Y := by
  ext i j; simp [Finset.sum_add_distrib]

theorem ptrB_smul [Fintype κ] (c : ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) : ptrB (c • X) = c • ptrB X := by
  ext i j; simp [Finset.mul_sum]

theorem ptrA_smul [Fintype ι] (c : ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) : ptrA (c • X) = c • ptrA X := by
  ext k l; simp [Finset.mul_sum]

/-! ## 保真引理 F1–F4：`ptrB` 是對的部分跡 -/

/-- **F1** 對偶刻畫：`ptrB` 是 `A ↦ A ⊗ 1` 對跡配對的伴隨。
這條讓定義與指標慣例無關：跡配對非退化，滿足它的映射只有一個。 -/
theorem trace_ptrB_mul [Fintype ι] [Fintype κ] [DecidableEq κ] (X : Matrix (ι × κ) (ι × κ) ℂ) (A : Matrix ι ι ℂ) :
    trace (ptrB X * A) = trace (X * (A ⊗ₖ (1 : Matrix κ κ ℂ))) := by
  simp only [trace, diag_apply, mul_apply, ptrB_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **F2** 乘積態：`Tr_B (A ⊗ B) = (tr B) · A`。 -/
theorem ptrB_kronecker [Fintype κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    ptrB (A ⊗ₖ B) = trace B • A := by
  ext i j
  simp only [ptrB_apply, kroneckerMap_apply, trace, diag_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **F3** 保跡。 -/
theorem trace_ptrB [Fintype ι] [Fintype κ] (X : Matrix (ι × κ) (ι × κ) ℂ) : trace (ptrB X) = trace X := by
  simp only [trace, diag_apply, ptrB_apply, Fintype.sum_prod_type]

/-- **F4** 保半正定：密度矩陣的約化仍是密度矩陣（配合 F3）。 -/
theorem ptrB_posSemidef [Fintype κ] {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) :
    (ptrB X).PosSemidef := by
  have h : ptrB X = ∑ k, X.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j; simp [Matrix.sum_apply]
  rw [h]
  exact posSemidef_sum _ fun k _ => hX.submatrix _

/-! ## 純態的約化 -/

/-- 純態的 A 側約化：`Tr_B |vec S⟩⟨vec S| = S Sᴴ`。 -/
theorem ptrB_pure [Fintype κ] (S : Matrix ι κ ℂ) :
    ptrB (vecMulVec (vecOf S) (star (vecOf S))) = S * Sᴴ := by
  ext i j
  simp only [ptrB_apply, vecMulVec_apply, vecOf_apply, Pi.star_apply, mul_apply,
    conjTranspose_apply]

/-- 純態的 B 側約化：`Tr_A |vec S⟩⟨vec S| = (Sᴴ S)ᵀ`。注意是轉置（T2 的轉置陷阱就從這裡來）。 -/
theorem ptrA_pure [Fintype ι] (S : Matrix ι κ ℂ) :
    ptrA (vecMulVec (vecOf S) (star (vecOf S))) = (Sᴴ * S)ᵀ := by
  ext k l
  simp only [ptrA_apply, vecMulVec_apply, vecOf_apply, Pi.star_apply, transpose_apply,
    mul_apply, conjTranspose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## 見證 F5–F6 -/

/-- 最大糾纏態 `|Ω⟩⟨Ω| / n`，其中 `|Ω⟩ = Σ_i |i⟩|i⟩ = vec 1`。`n = Fin 2` 即 Bell 態。 -/
def maxEnt (n : Type*) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  ((Fintype.card n : ℂ)⁻¹) •
    vecMulVec (vecOf (1 : Matrix n n ℂ)) (star (vecOf (1 : Matrix n n ℂ)))

/-- **F5** 最大糾纏態的 A 側約化是最大混合態。 -/
theorem ptrB_maxEnt (n : Type*) [Fintype n] [DecidableEq n] :
    ptrB (maxEnt n) = ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ) := by
  rw [maxEnt, ptrB_smul, ptrB_pure, conjTranspose_one, Matrix.mul_one]

theorem ptrA_maxEnt (n : Type*) [Fintype n] [DecidableEq n] :
    ptrA (maxEnt n) = ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ) := by
  rw [maxEnt, ptrA_smul, ptrA_pure, conjTranspose_one, Matrix.mul_one, transpose_one]

/-- **F6** `ptrB ≠ ptrA` 的見證：`|0⟩⟨0| ⊗ |1⟩⟨1|` 兩側的約化態不同。
擋「Tr_A 與 Tr_B 寫反」：若兩者被寫成同一個東西，這條會失敗。 -/
theorem ptrB_ne_ptrA_witness :
    ptrB (single (0 : Fin 2) 0 (1 : ℂ) ⊗ₖ single (1 : Fin 2) 1 (1 : ℂ)) ≠
      ptrA (single (0 : Fin 2) 0 (1 : ℂ) ⊗ₖ single (1 : Fin 2) 1 (1 : ℂ)) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [single_apply] at h00

/-! ## 保真引理 F7–F8：`idKron` 是對的 `id ⊗ Φ` -/

theorem blk_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (i j : ι) :
    blk (A ⊗ₖ B) i j = A i j • B := by
  ext k l; simp [kroneckerMap_apply]

/-- **F7** 乘積態上：`(id ⊗ Φ)(A ⊗ B) = A ⊗ Φ B`。 -/
theorem idKron_kronecker (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    idKron Φ (A ⊗ₖ B) = A ⊗ₖ Φ B := by
  ext p q; simp [blk_kronecker, kroneckerMap_apply]

/-- **F8** 唯一性：任何在乘積態上與 `id ⊗ Φ` 一致的線性映射，就是 `idKron Φ`。
所以 `idKron` 不只在乘積態上對，在糾纏態上也是唯一合理的延拓。 -/
theorem idKron_unique [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (L : Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × κ') (ι × κ') ℂ)
    (hL : ∀ (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ), L (A ⊗ₖ B) = A ⊗ₖ Φ B) :
    L = idKron Φ := by
  have hs : ∀ (p q : ι × κ) (c : ℂ), L (single p q c) = idKron Φ (single p q c) := by
    intro p q c
    have e : single p q c = single p.1 q.1 c ⊗ₖ single p.2 q.2 (1 : ℂ) := by
      rw [single_kronecker_single, mul_one]
    rw [e, hL, idKron_kronecker]
  refine LinearMap.ext fun X => ?_
  rw [matrix_eq_sum_single X]
  simp only [map_sum, hs]

end

end ErEpr
