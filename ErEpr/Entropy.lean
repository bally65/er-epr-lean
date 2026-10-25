import ErEpr.TFD
import ErEpr.MPS

/-!
# ErEpr.Entropy：von Neumann 熵（第二批）

* 定義：`vnEntropy ρ = -Σ λ log λ`，對特徵多項式的根（＝固有值，含重數）求和。
  Hermitian 的 `ρ` 上，它等於對 `eigenvalues` 求和（`vnEntropy_eq_sum_eigenvalues`）；
  非 Hermitian 的矩陣上這個定義沒有物理意義，本庫也不用。
* 健全性見證：
  * 實對角矩陣的熵是 Shannon 熵（`vnEntropy_diagonal`）；
  * d 維最大混合態的熵是 `log d`（`vnEntropy_maxMixed`）。
* **S ≤ log rank**：密度矩陣（半正定、跡為 1）的熵不超過 `log (rank ρ)`（`vnEntropy_le_log_rank`）。
* **純態 S(A) = S(B)**（`vnEntropy_ptrA_pureOf_eq`）：
  任何純態兩側約化態的熵相等，即使兩側維度不同、而且 B 側差一個轉置。
* 接 T3：歸一化 MPS 在切口的糾纏熵 ≤ |γ| log D：
  * 開邊界 `|γ| = 1`（`vnEntropy_cut_mpsOpen_le`）；
  * 環狀 `|γ| = 2`（`vnEntropy_cut_mpsRing_le`）；
  * Bell 對恰好等於 log 2（`vnEntropy_cut_bellN`）。
  * 環狀的兩組 Bell 對恰好等於 2 log 2（`vnEntropy_cut_ringBellN`）：環狀上界也是緊的。
* 接 T2：TFD 兩側的糾纏熵都等於 Gibbs 態的熵（`vnEntropy_ptrA_tfdState`）。

範圍（引用前請讀）：
* 這是 Ryu–Takayanagi 公式「≤」那一半的離散玩具版。上界對任何 MPS 都成立，包括與全像無關的網路；
  等號、極小曲面、全像對偶都沒有證明。
* 「TFD 糾纏熵 = 熱力學熵」是有限維矩陣事實；與黑洞熵（Bekenstein–Hawking）的對應，這裡沒有形式化。

設計見 `DESIGN.md` §8（第二批）。
-/

namespace ErEpr

open Matrix Polynomial
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 定義 -/

/-- von Neumann 熵 `S(ρ) = -Σ λ log λ`，對特徵多項式的根（含重數）求和；`0 log 0 = 0`。 -/
def vnEntropy (ρ : Matrix n n ℂ) : ℝ :=
  (ρ.charpoly.roots.map fun z => Real.negMulLog z.re).sum

/-- Hermitian 矩陣上，熵就是對固有值求 `-λ log λ` 的和。 -/
theorem vnEntropy_eq_sum_eigenvalues {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vnEntropy ρ = ∑ i, Real.negMulLog (hρ.eigenvalues i) := by
  rw [vnEntropy, hρ.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1

/-- **健全性**：實對角矩陣的熵就是 Shannon 熵。 -/
theorem vnEntropy_diagonal (d : n → ℝ) :
    vnEntropy (diagonal fun i => (d i : ℂ)) = ∑ i, Real.negMulLog (d i) := by
  rw [vnEntropy, charpoly_diagonal, roots_prod _ _
    (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _).ne_zero]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  congr 1

/-- 純量矩陣 `a · 1` 的熵。 -/
theorem vnEntropy_smul_one (a : ℝ) :
    vnEntropy ((a : ℂ) • (1 : Matrix n n ℂ)) = Fintype.card n * Real.negMulLog a := by
  rw [smul_one_eq_diagonal, vnEntropy_diagonal (fun _ => a), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- **健全性**：d 維最大混合態 `1/d` 的熵是 `log d`。 -/
theorem vnEntropy_maxMixed [Nonempty n] :
    vnEntropy ((((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) =
      Real.log (Fintype.card n) := by
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [vnEntropy_smul_one, Real.negMulLog, Real.log_inv, neg_mul_neg, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]

/-- 最大糾纏態的 A 側糾纏熵是 `log d`。 -/
theorem vnEntropy_ptrB_maxEnt [Nonempty n] :
    vnEntropy (ptrB (maxEnt n)) = Real.log (Fintype.card n) := by
  rw [ptrB_maxEnt, ← vnEntropy_maxMixed]
  congr 2
  simp

/-! ## S ≤ log rank -/

/-- 跡為 1 的半正定矩陣，秩至少 1。 -/
theorem rank_pos_of_posSemidef_trace_one {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) : 0 < ρ.rank := by
  rw [hρ.1.rank_eq_card_non_zero_eigs, Fintype.card_pos_iff]
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : ∀ i, hρ.1.eigenvalues i = 0 := fun i => by
    by_contra hi
    exact h.false ⟨i, hi⟩
  have ht := hρ.1.trace_eq_sum_eigenvalues
  rw [htr] at ht
  simp [h0] at ht

/-- **S ≤ log rank**：密度矩陣（半正定、跡 1）的 von Neumann 熵不超過 `log (rank ρ)`。
證法：只在非零固有值上求和，再用 `-x log x` 的凹性（Jensen）。 -/
theorem vnEntropy_le_log_rank {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy ρ ≤ Real.log ρ.rank := by
  classical
  set ev := hρ.1.eigenvalues with hev
  have hnn : ∀ i, 0 ≤ ev i := hρ.eigenvalues_nonneg
  have hsum : ∑ i, ev i = 1 := by
    have h := hρ.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    apply Complex.ofReal_injective
    push_cast
    exact h.symm
  set S := Finset.univ.filter fun i => ev i ≠ 0 with hS
  have hrank : ρ.rank = S.card := by
    rw [hρ.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hzero : ∀ f : ℝ → ℝ, f 0 = 0 → ∑ i ∈ S, f (ev i) = ∑ i, f (ev i) := by
    intro f hf
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not.mp h, hf]
  have hS_sum : ∑ i ∈ S, ev i = 1 := by
    have h := hzero (fun x => x) rfl
    rw [h, hsum]
  have hent : vnEntropy ρ = ∑ i ∈ S, Real.negMulLog (ev i) := by
    rw [vnEntropy_eq_sum_eigenvalues hρ.1, hzero Real.negMulLog Real.negMulLog_zero]
  have hcard : 0 < S.card := by
    rw [Finset.card_pos]
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hS_sum
    exact zero_ne_one hS_sum
  set c : ℝ := (S.card : ℝ)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hcard)
  have hw : ∑ _i ∈ S, c = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcard.ne')]
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := S) (w := fun _ => c) (p := ev)
    (fun _ _ => hc0.le) hw (fun i _ => Set.mem_Ici.mpr (hnn i))
  simp only [smul_eq_mul, ← Finset.mul_sum, hS_sum, mul_one] at hJ
  have hneg : Real.negMulLog c = c * Real.log S.card := by
    rw [Real.negMulLog, hc, Real.log_inv]
    ring
  rw [hneg] at hJ
  rw [hent, hrank]
  exact le_of_mul_le_mul_left hJ hc0

/-- 配合秩的上界使用：`rank ρ ≤ R` 時 `S(ρ) ≤ log R`。 -/
theorem vnEntropy_le_log_of_rank_le {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) {R : ℕ} (hR : ρ.rank ≤ R) : vnEntropy ρ ≤ Real.log R :=
  (vnEntropy_le_log_rank hρ htr).trans
    (Real.log_le_log (Nat.cast_pos.mpr (rank_pos_of_posSemidef_trace_one hρ htr))
      (Nat.cast_le.mpr hR))

/-- **N8** 歸一化不能拿掉：未歸一化的 `diag(1/e, 1/e)`（跡 2/e ≠ 1）熵是 2/e ≈ 0.736，
大於 log(rank) = log 2 ≈ 0.693。所以 `vnEntropy_le_log_rank` 的 `trace ρ = 1` 是必要的。 -/
theorem negctrl_unnormalized :
    Real.log (diagonal fun _ : Fin 2 => ((Real.exp (-1) : ℝ) : ℂ)).rank <
      vnEntropy (diagonal fun _ : Fin 2 => ((Real.exp (-1) : ℝ) : ℂ)) := by
  classical
  have hr : (diagonal fun _ : Fin 2 => ((Real.exp (-1) : ℝ) : ℂ)).rank = 2 := by
    rw [Matrix.rank_diagonal]
    simp
  rw [hr, vnEntropy_diagonal (fun _ => Real.exp (-1)), Fin.sum_univ_two, Real.negMulLog,
    Real.log_exp]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.log_two_lt_d9
  have h3 : 1 / 2.7182818286 < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (Real.exp_pos 1)).mpr h1
  push_cast
  linarith

/-! ## 純態 S(A) = S(B) -/

/-- 在根的多重集裡多放幾個 0，熵不變（`0 log 0 = 0`）。 -/
theorem roots_entropy_X_pow_mul (p : ℂ[X]) (hp : p ≠ 0) (k : ℕ) :
    ((X ^ k * p).roots.map fun z : ℂ => Real.negMulLog z.re).sum =
      (p.roots.map fun z : ℂ => Real.negMulLog z.re).sum := by
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp), roots_X_pow, Multiset.map_add,
    Multiset.sum_add, Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
    Multiset.sum_singleton]
  simp

/-- `S(AB) = S(BA)`：`AB` 與 `BA` 的非零固有值（含重數）相同。 -/
theorem vnEntropy_mul_comm {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) : vnEntropy (A * B) = vnEntropy (B * A) := by
  rw [vnEntropy, vnEntropy,
    ← roots_entropy_X_pow_mul _ (A * B).charpoly_monic.ne_zero (Fintype.card n),
    charpoly_mul_comm', roots_entropy_X_pow_mul _ (B * A).charpoly_monic.ne_zero]

theorem vnEntropy_transpose (ρ : Matrix n n ℂ) : vnEntropy ρᵀ = vnEntropy ρ := by
  rw [vnEntropy, vnEntropy, charpoly_transpose]

/-- **純態 S(A) = S(B)**：任何純態 `pureOf M` 兩側約化態的熵相等。
兩側維度可以不同，B 側還差一個轉置。 -/
theorem vnEntropy_ptrA_pureOf_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℂ) :
    vnEntropy (ptrA (pureOf M)) = vnEntropy (ptrB (pureOf M)) := by
  rw [ptrA_pureOf, ptrB_pureOf, ← transpose_smul, vnEntropy_transpose, ← Matrix.smul_mul,
    ← Matrix.mul_smul, vnEntropy_mul_comm]

/-- 接 T2：TFD 的 B 側約化態是 Gibbs 態的轉置，但糾纏熵仍等於 Gibbs 態的熵。 -/
theorem vnEntropy_ptrA_tfdState {H : Matrix n n ℂ} (hH : H.IsHermitian) (β : ℝ) :
    vnEntropy (ptrA (tfdState hH β)) = vnEntropy (gibbs H β) := by
  rw [tfdState, vnEntropy_ptrA_pureOf_eq, ← tfdState, ptrB_tfdState]

/-! ## 接 T3：熵 ≤ |γ| log D -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {D : ℕ}

/-- **熵版 T3a**：歸一化的開邊界 MPS，切口處 A 側的糾纏熵 ≤ log D（割 1 條鍵）。 -/
theorem vnEntropy_cut_mpsOpen_le {k m : ℕ} (l r : Fin D → ℂ)
    (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ)
    (hnorm : trace (cutAt k m (mpsOpen l r A) * (cutAt k m (mpsOpen l r A))ᴴ) = 1) :
    vnEntropy (ptrB (vecMulVec (vecOf (cutAt k m (mpsOpen l r A)))
      (star (vecOf (cutAt k m (mpsOpen l r A)))))) ≤ Real.log D := by
  rw [ptrB_pure]
  refine vnEntropy_le_log_of_rank_le (posSemidef_self_mul_conjTranspose _) hnorm ?_
  rw [rank_self_mul_conjTranspose]
  exact rank_cutAt_mpsOpen_le l r A

/-- **熵版 T3b**：歸一化的環狀 MPS，切口處 A 側的糾纏熵 ≤ 2 log D（割 2 條鍵）。 -/
theorem vnEntropy_cut_mpsRing_le {k m : ℕ} (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ)
    (hnorm : trace (cutAt k m (mpsRing A) * (cutAt k m (mpsRing A))ᴴ) = 1) :
    vnEntropy (ptrB (vecMulVec (vecOf (cutAt k m (mpsRing A)))
      (star (vecOf (cutAt k m (mpsRing A)))))) ≤ 2 * Real.log D := by
  rw [ptrB_pure]
  have h := vnEntropy_le_log_of_rank_le (posSemidef_self_mul_conjTranspose _) hnorm
    (R := D ^ 2) (by rw [rank_self_mul_conjTranspose]; exact rank_cutAt_mpsRing_le A)
  rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h

/-! ## 緊度見證：歸一化的 Bell MPS 熵恰為 log 2 -/

omit [Fintype σ] [DecidableEq σ] in
theorem cutAt_mpsOpen_smul {k m : ℕ} (c : ℂ) (l r : Fin D → ℂ)
    (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    cutAt k m (mpsOpen (c • l) r A) = c • cutAt k m (mpsOpen l r A) := by
  ext y z
  simp [cutAt, mpsOpen, smul_dotProduct]

/-- 歸一化係數 `1/√2`。 -/
def sBell : ℝ := (Real.sqrt 2)⁻¹

theorem sBell_mul_self : sBell * sBell = 1 / 2 := by
  rw [sBell, ← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]

/-- 歸一化 Bell MPS 的切口：`Ψ Ψᴴ = (1/2) · 1`。 -/
theorem cutAt_bellN_mul_conjTranspose :
    cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA) *
        (cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA))ᴴ =
      ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) := by
  rw [cutAt_mpsOpen_smul, cutAt_bell, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sBell_mul_self]
  simp

/-- 歸一化 Bell MPS 確實歸一：`tr(Ψ Ψᴴ) = 1`。 -/
theorem trace_bellN : trace (cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA) *
    (cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA))ᴴ) = 1 := by
  rw [cutAt_bellN_mul_conjTranspose, trace_smul, trace_one]
  simp

/-- **緊度見證**：歸一化 Bell MPS（D = 2）切口的糾纏熵恰好是 log 2 = log D，熵版 T3a 的上界達得到。 -/
theorem vnEntropy_cut_bellN :
    vnEntropy (ptrB (vecMulVec (vecOf (cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA)))
      (star (vecOf (cutAt 1 1 (mpsOpen ((sBell : ℂ) • e0) e0 bellA)))))) = Real.log 2 := by
  rw [ptrB_pure, cutAt_bellN_mul_conjTranspose, vnEntropy_smul_one, Real.negMulLog]
  simp

/-! ## 緊度見證：歸一化的環狀 Bell MPS 熵恰為 2 log 2 -/

omit [Fintype σ] [DecidableEq σ] in
/-- 每個格點的張量都乘上 `c`，鏈乘積乘上 `c ^ n`。 -/
theorem chainProd_smul {n : ℕ} (c : ℂ) (A : Fin n → σ → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → σ) : chainProd (c • A) x = c ^ n • chainProd A x := by
  induction n with
  | zero => simp [chainProd]
  | succ n ih =>
    have h := ih (fun i => A i.succ) (fun i => x i.succ)
    simp only [chainProd, Pi.smul_apply] at h ⊢
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h, smul_mul_smul_comm,
      pow_succ']

omit [Fintype σ] [DecidableEq σ] in
/-- 環狀 MPS 的純量縮放：每個格點的張量都乘上 `c`，切口矩陣乘上 `c ^ (k + m)`。 -/
theorem cutAt_mpsRing_smul {k m : ℕ} (c : ℂ) (A : Fin (k + m) → σ → Matrix (Fin D) (Fin D) ℂ) :
    cutAt k m (mpsRing (c • A)) = c ^ (k + m) • cutAt k m (mpsRing A) := by
  ext y z
  simp only [cutAt, mpsRing, of_apply, chainProd_smul, trace_smul, Matrix.smul_apply]

/-- 歸一化的環狀 Bell MPS：兩個格點的張量都乘上 `1/√2`，振幅整體乘上 `1/2`，
切口矩陣是 `(1/2) · 1₄`（`‖vec 1₄‖² = 4`）。 -/
theorem cutAt_ringBellN :
    cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA)) =
      ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 1 → Fin 2 × Fin 2) (Fin 1 → Fin 2 × Fin 2) ℂ) := by
  rw [cutAt_mpsRing_smul, cutAt_ringBell, ← sBell_mul_self]
  congr 1
  push_cast
  ring

/-- 歸一化環狀 Bell MPS 的切口：`Ψ Ψᴴ = (1/4) · 1₄`。 -/
theorem cutAt_ringBellN_mul_conjTranspose :
    cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA)) *
        (cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA)))ᴴ =
      ((1 / 4 : ℝ) : ℂ) • (1 : Matrix (Fin 1 → Fin 2 × Fin 2) (Fin 1 → Fin 2 × Fin 2) ℂ) := by
  rw [cutAt_ringBellN, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, smul_smul]
  congr 1
  norm_num

/-- 歸一化環狀 Bell MPS 確實歸一：`tr(Ψ Ψᴴ) = 1`。 -/
theorem trace_ringBellN : trace (cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA)) *
    (cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA)))ᴴ) = 1 := by
  rw [cutAt_ringBellN_mul_conjTranspose, trace_smul, trace_one]
  norm_num

/-- **緊度見證**：歸一化環狀 Bell MPS（D = 2）切口的糾纏熵恰好是 2 log 2 = log D²，
熵版 T3b 的上界 2 log D 達得到。 -/
theorem vnEntropy_cut_ringBellN :
    vnEntropy (ptrB (vecMulVec (vecOf (cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA))))
      (star (vecOf (cutAt 1 1 (mpsRing ((sBell : ℂ) • ringBellA))))))) = 2 * Real.log 2 := by
  rw [ptrB_pure, cutAt_ringBellN_mul_conjTranspose, vnEntropy_smul_one, Real.negMulLog]
  have hc : Fintype.card (Fin 1 → Fin 2 × Fin 2) = 4 := by simp
  have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hc, h4]
  push_cast
  ring

end

end ErEpr
