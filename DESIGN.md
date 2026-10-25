# ER=EPR 玩具零件：Lean 4 設計 v0

- 日期：2026-10-23
- 狀態：**第一批（§2 Basic、§3 T1、§4 T2、§5 T3）與第二批（von Neumann 熵）都已在 lean-node 編譯通過**（2026-10-23，證據見 `EVIDENCE.md`）。
- 第二批實作：
  - 熵用特徵多項式的根定義，不需要帶 Hermitian 證明。另證它等於對固有值求和。
  - S(A) = S(B) 走 `charpoly_mul_comm'` 和 `charpoly_transpose`。
  - S ≤ log rank 走 `concaveOn_negMulLog` 的 Jensen 不等式。
  - MPS 熵上界用歸一化假設 `tr(ΨΨᴴ) = 1`。這個假設能夠成立，由歸一化 Bell MPS 見證。
- T3 實作與 §5 草稿的差異：
  - 切口寫成 `cutAt k m`，配合 `Fin.append`；鏈長固定為 `k + m`。
  - 切分走 `List.ofFn_add` 與 `List.prod_append`。
  - 另證約化密度矩陣的秩等於 Schmidt 秩。
  - 環狀上界 D² 是否緊，沒有見證。
- T2 實作與 §4 草稿的差異：
  - `tfdAmp` 寫成矩陣形式 `U · diag · Uᴴ`，U 是 `eigenvectorUnitary`。
  - 歸一化用態自己的範數平方 `tr(M Mᴴ)`，放在 `pureOf` 裡。
  - 另證 `trace_tfdState = 1`，確保不是「0 = 0」；這條需要 `ι` 非空。
  - T2d（boost 不變性）沒做。
  - TFD.lean 關掉了 `unnecessarySeqFocus` 風格 linter。
  - R4 演習沒驗到「T2a 照過、只有 T2b 紅」，見 EVIDENCE。
- 實作與 §2、§3 草稿的差異：
  - `idKron` 做成 `LinearMap`。
  - 最大糾纏態 `maxEnt n` 一般化到任意 n，Bell 態是 n = Fin 2 的特例。
  - Kraus 的推論改走 `sandwich` 加上 F8 唯一性。
  - 負控制寫成具名 theorem，不用 `example`，這樣才能檢查公理。
- 來源：三方討論兩輪（物理／量子資訊、Lean 工程、懷疑者稽核），主線裁決。
- mathlib 名字：凡標「✓」的，都已在本機 mathlib 樹（v4.32.0-rc1）用 grep 確認存在。

---

## 0. 這個庫是什麼（README 範圍聲明草稿）

這個庫在有限維複矩陣上形式化三個量子資訊事實：
1. 對一側施加保跡線性映射，另一側的約化態不變。
2. 熱場雙態（TFD）的單邊約化態是 Gibbs 態，另一邊是它的轉置。
3. 矩陣乘積態（MPS）跨切口的 Schmidt 秩，上界是鍵維度的「割邊數」次方。

它們是 ER=EPR 字典裡 **EPR 側的玩具零件**。ER 側的座標層級零件後來另外加上，見 §10；ER 側沒有流形上的幾何，也沒有證明 Einstein 方程。

ER=EPR 與 Ryu–Takayanagi 是量子重力的物理猜想，本身不是數學命題。這個庫不證它們，也不聲稱驗證了它們。

其他範圍限制：
- 通道主定理只要求「線性＋保跡」，沒有證輸出仍是量子態（那需要完全正性）。
- Choi–Kraus 等價沒有形式化。
- 物理名詞只出現在 docstring，不進定理名。
- 上游已有量子資訊 Lean 庫（見 §9），本庫不宣稱是第一個。

---

## 1. 裁決表

| # | 議題 | 裁決 | 三方立場 |
|---|---|---|---|
| D1 | 通道表示 | 主定理用「ℂ-線性＋保跡」配逐塊延拓 `idKron`；Kraus 版退為推論，另證 `Kraus.app = idKron` | 三方同意 |
| D2 | 保真引理 | §2 的 F1–F8 全部必做，缺一條該定理不算完成 | 三方逐輪補齊 |
| D3 | 熱態定義 | 熱態用矩陣指數 `NormedSpace.exp` 獨立定義；TFD 振幅用固有向量建構；兩者相等才算有內容。左右兩側分開寫，用 σ_y 負控制擋轉置陷阱 | 三方同意（第一輪 E 原用 cfc，已讓步） |
| D4 | 張量網路做到哪 | 單獨的因式分解引理只當輔助，不算成果。成果是 MPS：開邊界（割 1 條鍵，秩 ≤ D）＋環狀（割 2 條，秩 ≤ D²）＋Bell 緊度見證。一般圖的「∀割」版延後 | S、E 主張 MPS，P 主張一般圖；環狀 MPS 是主線補的折衷，用來讓「次方＝割邊數」有實質內容 |
| D5 | 函式庫 | 自建，toolchain 跟 v4.32.0-rc1。命名慣例對齊上游，方便日後交叉核對。公開前要在節點上 grep physlib 全庫 | 三方同意（S 查證後改口） |
| D6 | 順序 | Basic＋T1（含 `ptrB_pure`）→ T2 → T3 | P、S 主張 1→2→3，E 主張 1→3→2。主線取多數；T2 卡關時的停損見 §4 |
| D7 | 第二批 | **使用者 2026-10-23 拍板：S_vN ≤ log rank＋純態 S(A) = S(B)** | P：隱形傳態；S：單子性；E：S_vN ≤ log rank |

---

## 2. 定義層 `ErEpr/Basic.lean`

```lean
open Matrix Kronecker
variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ'] [DecidableEq ι] [DecidableEq κ]

/-- 對右因子取跡：保留左因子。 -/
def ptrB (X : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  .of fun i j => ∑ k, X (i, k) (j, k)

/-- 對左因子取跡：保留右因子。用 swap 重排後套 ptrB，不另開 API。 -/
def ptrA (X : Matrix (ι × κ) (ι × κ) ℂ) : Matrix κ κ ℂ :=
  ptrB (X.submatrix Prod.swap Prod.swap)

def blk (X : Matrix (ι × κ) (ι × κ) ℂ) (i j : ι) : Matrix κ κ ℂ :=
  .of fun k l => X (i, k) (j, l)

/-- id ⊗ Φ：在每個 (i,j) 區塊上套 Φ。 -/
def idKron (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    Matrix (ι × κ') (ι × κ') ℂ :=
  .of fun p q => Φ (blk X p.1 q.1) p.2 q.2
```

**保真引理**（每條都是為了擋某種「定義寫錯但定理照樣綠」的情況）：

| 編號 | 陳述（草稿） | 擋什麼 |
|---|---|---|
| F1 | `trace (ptrB X * A) = trace (X * (A ⊗ₖ 1))` | 對偶刻畫，讓 ptrB 的定義與慣例無關 |
| F2 | `ptrB (A ⊗ₖ B) = trace B • A` | 乘積態行為 |
| F3 | `trace (ptrB X) = trace X` | 保跡 |
| F4 | `X.PosSemidef → (ptrB X).PosSemidef` | 「約化密度矩陣」名實相符 |
| F5 | `ptrB bell = (1/2 : ℂ) • 1`（Fin 2） | 具體見證 |
| F6 | 取 X = \|0⟩⟨0\| ⊗ \|1⟩⟨1\|（ι = κ = Fin 2）：`ptrB X ≠ ptrA X` | 擋 Tr_A／Tr_B 對調 |
| F7 | `idKron Φ (A ⊗ₖ B) = A ⊗ₖ Φ B` | 擋 idKron 忽略 Φ |
| F8 | ℂ-線性 L 若滿足 ∀A B, `L (A ⊗ₖ B) = A ⊗ₖ Φ B`，則 `L = idKron Φ` | 擋「只對乘積態對」；證法用 `single_kronecker_single` ✓ 展開 |

選做：idKron 對複合的函子性（P 提議）。

為什麼 F7、F8 是重點：T1 的證明只用到保跡，連 Φ 的線性都沒用上（主線手驗）。所以 T1 本身幾乎是把定義展開；`idKron` 真的等於 id⊗Φ，要靠 F7、F8 來保證。

---

## 3. T1 不可通訊 `ErEpr/NoSignalling.lean`

```lean
theorem ptrB_idKron (Φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix κ' κ' ℂ)
    (hTP : ∀ M, trace (Φ M) = trace M) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ptrB (idKron Φ X) = ptrB X

structure Kraus (κ r : Type*) [Fintype κ] [Fintype r] where
  K  : r → Matrix κ κ ℂ
  tp : ∑ a, (K a)ᴴ * K a = 1        -- 注意是 Kᴴ K（保跡），不是 K Kᴴ（unital）

theorem Kraus.app_eq_idKron (Φ : Kraus κ r) (X) :
    ∑ a, (1 ⊗ₖ Φ.K a) * X * (1 ⊗ₖ Φ.K a)ᴴ = idKron Φ.toLin X
theorem no_signalling_kraus (Φ : Kraus κ r) (X) : ptrB (Φ.app X) = ptrB X
```

- 工程估計：主定理約 4–6 行，F7 約 5 行，F8 約 10–15 行，Kraus 推論約 16 行。這些都是估計，還沒驗證。
- 會用到的名字：`trace_mul_cycle` ✓、`mul_kronecker_mul` ✓、`conjTranspose_kronecker`、`trace_kronecker` ✓。

**負控制**（`example : ¬ …` 或 `≠`，每條不超過 10 行）：

| 編號 | 內容 | 驗什麼 |
|---|---|---|
| N1 | Φ = 0（不保跡）配 Bell 態，結論為假 | hTP 不能刪 |
| N2 | Kraus 族 K₁ = \|0⟩⟨0\|、K₂ = \|1⟩⟨0\|：Σ K Kᴴ = 1，但 Σ Kᴴ K = 2\|0⟩⟨0\|。配 Bell 態，ptrB 由 I/2 變成 \|0⟩⟨0\| | 擋把 unital 誤當保跡（主線手驗過） |
| N3 | B 上的置換通道 Φ(M) = tr M · \|0⟩⟨0\|：ptrB 不變，但 ptrA 會變 | 結論不是「所有邊際都不變」 |
| N4 | 改對 A 側施通道（把 A 重置成 \|0⟩），ptrB 必變 | 局域性是必要的 |

**見證**（所有假設都滿足、定理成立）：
- Pauli X。
- amplitude damping：保跡但不 unital。
- 轉置映射：保跡但不完全正。docstring 要註明它不是物理通道，所以本定理不刻畫「通道」。

可說／不可說：
- 可說：任何 ℂ-線性保跡的局部映射，都不改變另一方的約化態。
- 不可說：證明了 ER 橋不可穿越。那是重力端的拓撲審查定理（Friedman–Schleich–Witt 1993），這裡沒有形式化。

---

## 4. T2 熱場雙態 `ErEpr/TFD.lean`

```lean
variable {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ)

/-- 熱態：用矩陣指數定義，不經譜分解。 -/
def gibbs (H : Matrix ι ι ℂ) (β : ℝ) : Matrix ι ι ℂ :=
  (trace (NormedSpace.exp (-(β : ℂ) • H)))⁻¹ • NormedSpace.exp (-(β : ℂ) • H)

/-- TFD 振幅：用固有向量建構，即物理書的 Σ e^{-βE_n/2} |n⟩⟨n|。 -/
def tfdAmp : Matrix ι ι ℂ :=
  ∑ n, (Real.exp (-β * hH.eigenvalues n / 2) : ℂ) •
    vecMulVec (hH.eigenvectorBasis n) (star (hH.eigenvectorBasis n))

def vecOf (S : Matrix ι κ ℂ) : ι × κ → ℂ := fun p => S p.1 p.2
-- |TFD⟩ = vecOf(tfdAmp)/√Z。
-- vecOf(Σ c_n u_n u_nᴴ) = Σ c_n u_n ⊗ ū_n：右側是複共軛，這個定義自動滿足。
```

| 編號 | 陳述 | 說明 |
|---|---|---|
| T2a | `ptrB (tfdState) = gibbs H β` | 左側約化態＝Gibbs 態 |
| T2b | `ptrA (tfdState) = (gibbs H β)ᵀ` | 右側是轉置。寫 `ᵀ`，不寫共軛 |
| T2c | β ≠ 0 → `gibbs σ_y β ≠ (gibbs σ_y β)ᵀ` | 轉置陷阱的見證 |
| T2d（選做） | `(H ⊗ₖ 1 - 1 ⊗ₖ Hᵀ) *ᵥ tfd = 0` | 對應 Kruskal boost 對稱 |

**橋接引理**（最大風險）：`tfdAmp * tfdAmpᴴ = exp(−βH)`。
- mathlib 沒有矩陣版的 exp 與 `IsHermitian.cfc` 互通的引理（工程 grep：Analysis/Matrix/ 下 exp 為 0 筆）。
- 通用的 `CFC.exp_eq_normedSpace_exp` ✓ 需要範數實例，能不能直接套用還沒實測。
- 推薦路線是繞開 cfc：
  1. 用 `spectral_theorem` ✓ 寫成 H = U·diag(λ)·Uᴴ。
  2. 用 `Matrix.exp_conj` ✓（要 IsUnit U）。
  3. 用 `Matrix.exp_diagonal` ✓。
  4. 用 `IsHermitian.exp` ✓。
  5. 用 `exp_add_of_commute` ✓ 處理 e^{-βH/2}·e^{-βH/2}。
- **停損**：橋接若超出預算，先跳到 T3，T2 標記為開放。不准退回「H 取對角」充當完成，因為那樣轉置陷阱看不見，等於把定理掏空。

主線手算了轉置（與物理角色獨立算出的一致）。設 ψ(i,j) = M_ij：
- ptrB ψψᴴ = M Mᴴ
- ptrA ψψᴴ = (Mᴴ M)ᵀ

取 M = e^{−βH/2}，兩者分別是 e^{−βH} 和 e^{−βHᵀ}。H = σ_y 時兩側的約化態分別是 (1 ∓ tanh β·σ_y)/2，確實不同。

**負控制與見證**：

| 編號 | 內容 |
|---|---|
| N5 | H = σ_y：「ptrA tfd = gibbs」可證偽（由 T2b＋T2c 得出） |
| N6 | 把 β 的符號弄反：H = diag(0,1)、β = ln 2，得 diag(1/3, 2/3)，不等於正確值 |
| N7 | 振幅漏掉 1/2：得 gibbs(2β)，不等於 gibbs(β) |
| W | H = diag(0,1)、β = ln 2，得 diag(2/3, 1/3) |
| R4（反向演習） | 把振幅右側改成 u_n 而不是 ū_n。T2a 照樣會過，T2b、T2d 必須紅燈。這正是 T2b 非寫不可的原因 |

可說／不可說：
- 可說：有限維 TFD 是純態，單邊約化恰為 Gibbs 態，另一側是它的轉置。
- 不可說：證明了「雙邊黑洞＝TFD」。那是全像論證（Israel 1976；Maldacena 2003），這裡沒有形式化。

---

## 5. T3 MPS 秩界 `ErEpr/MPS.lean`

- 輔助引理（不算成果）：`(L * R).rank ≤ Fintype.card γ`，由 `rank_mul_le_left` 與 `rank_le_card_width` 得出。
- MPS 定義：振幅 ψ(σ) = `(List.ofFn fun i => A i (σ i)).prod`。開邊界要夾上邊界向量；環狀則取 trace。切分時用 `List.prod_append`；`List.ofFn` 的切分引理名還沒確認。

| 編號 | 陳述 | 割邊數 |
|---|---|---|
| T3a | 開邊界 MPS 在第 k 個位置切開：`rank (reshape ψ) ≤ D` | 1 |
| T3b | 環狀 MPS 切成兩段連續區間：`rank ≤ D ^ 2` | 2 |
| W | Bell 對（D = 2）的秩恰好是 2 | 驗證上界緊 |

- 會用到的名字：`Fintype.card_fun` ✓（Data/Fintype/BigOperators.lean）。
- 命名：`rank_le_bond_pow_cut`。RT 只出現在 docstring。
- 第一批只講「秩」（Rényi-0 熵）。在 S_vN 做出來之前，不叫 entropy。

可說／不可說：
- 可說：MPS 跨切口的糾纏（以秩計）不超過 D 的割邊數次方。這是 RT 公式「≤」那一半的離散玩具版。
- 不可說：驗證了 RT。等號、最小割＝極小曲面、全像對偶都沒有證明；而且這個上界對非全像的網路同樣成立。

---

## 6. 完成判準（每顆定理）

1. 在 **lean-node** 上編譯通過。不在 Mac 上編。
2. `#print axioms` 只出現標準三公理。
3. 該定理的保真引理、負控制、見證全部編譯通過。
4. 反向演習：照下表把定義故意改壞，主定理或保真引理必須紅燈。

| 編號 | 改壞的方式 | 必須紅燈的地方 |
|---|---|---|
| R1 | ptrB 的求和指標對調 | F1 或 F6 |
| R2 | idKron 忽略 Φ | F7 |
| R3 | 刪掉 hTP | T1 編不過 |
| R4 | TFD 右側改用 u_n（見 §4） | T2b、T2d |
| R5 | gibbs 的 β 改成正號 | W |

5. 回報時只能說「已在節點編過」或「未編」。草稿不能當作定理。

---

## 7. 檔案結構

```
er_epr_lean/
  lean-toolchain        # leanprover/lean4:v4.33.1
  ErEpr/Basic.lean        §2（已完成）
  ErEpr/NoSignalling.lean §3（已完成）
  ErEpr/Axioms.lean       公理檢查
  ErEpr/TFD.lean          §4（已完成，T2d 未做）
  ErEpr/MPS.lean          §5（已完成）
  ErEpr/Entropy.lean      第二批（已完成）
  tools/node_run.sh     # Mac → lean-node 單行道
  tools/run_probe.sh    # 節點上執行
  evidence/             # 收回的證據
  DESIGN.md  EVIDENCE.md  README.md
```

版本改用節點現成的 Lean 4.33.1 與 mathlib `0df444a`，不再用文件開頭寫的 v4.32.0-rc1，好處是節點上不必另裝東西。本機可以 grep 的同版 mathlib 原始碼在 `alloy_engine/formal/lean/chemical_quantum/.lake/packages/mathlib`。

目前沒有 lakefile，做法同 `ecdsa_nonce_lean`，借用 mathlib 的 olean 編譯。之後要公開時再補 lakefile。

負控制寫成具名 theorem，放在各檔裡。

---

## 8. 待使用者決定

1. **第二批選哪一顆**：已決定，2026-10-23 使用者選第一列。以下保留當時的比較。

| 候選 | 對應 ER=EPR 的哪一面 | 代價 | 提議者 |
|---|---|---|---|
| S_vN ≤ log rank，加上純態 S(A) = S(B) | 把 T3 從「秩」升級成「熵 ≤ \|γ\| log D」（面積律的形狀）；也讓 TFD 兩側的熵相等，儘管兩側差一個轉置 | 低到中，需要的名字都已確認（`rank_eq_card_non_zero_eigs` ✓、`concaveOn_negMulLog`） | E |
| 量子隱形傳態，與 T1 配對 | 可穿越蟲洞（Gao–Jafferis–Wall 2017）的資訊骨架：收到古典訊息之前，Bob 的態是 I/d | 中（qubit 版） | P |
| 純態單子性：ρ_AB 純 ⇒ ρ_ABC = ρ_AB ⊗ ρ_C | AMPS 防火牆論證的核心 | 中到高 | S |

   主線推薦第一列，理由是它直接補強第一批的 T3 與 T2。

2. 專案位置與名稱：暫定 `~/Documents/alloy/er_epr_lean/`。
3. 何時開工：需要排用 lean-node。

公開與否之後再談，照「一次發一件、本人看完講得出來」的規則。

---

## 9. 上游查證

懷疑者第二輪用 WebFetch 讀原始檔。WebFetch 回傳的是摘要，不是 grep，所以「未見」只代表該檔內沒看到，不代表全庫都沒有。

| 上游 | 有什麼 | 未見 |
|---|---|---|
| Lean-Quantum，arXiv [2607.05492](https://arxiv.org/abs/2607.05492)，repo [Hayata-Yamasaki-Group/lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum) | partial trace、Choi、Kraus、Stinespring、資料處理不等式（DPI） | 不可通訊、Schmidt、熱態、張量網路 |
| [physlib QuantumInfo](https://github.com/leanprover-community/physlib/tree/master/QuantumInfo)（toolchain v4.35.0） | CPTP.lean 有 traceLeft／traceRight；MatrixMap 的 `kron` 用 TensorProduct 定義 | 邊際保持定理 |
| [Timeroot/Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo)（README 稱 2026-03 已併入 physlib） | 標量熱力學量；Sᵥₙ | Gibbs 密度矩陣、TFD；TODO.md 裡 Schmidt 分解標為未做 |

---

## 10. ER 側（2026-10-23 起）

mathlib（0df444a）沒有 Levi-Civita、Christoffel、偽黎曼／Lorentz 度規，也沒有 Riemann 曲率與 Lambert W，所以 ER 側一律在顯式座標裡做。

| 段 | 內容 | 狀態 |
|---|---|---|
| ER-1 | Kruskal 兩外區因果不相連；在內區相遇；類空曲線連通兩外區 | **完成**（`ER.lean`） |
| ER-2 | 喉部面積 ≥ 16πM²，在 ρ = M/2 達到；反演 ρ ↦ M²/4ρ 保持係數 | **完成** |
| ER-3 | 歐氏光滑性推出 β = 8πM | **完成**（`Hawking.lean`，3 輪，沒有觸發停損） |
| 收尾 | dS = dM/T 積分得 S = 4πM² = A/4；兩欄字典表 | **完成**（`first_law_area`，字典表在 README） |
| ER-4 | 自建座標版的 Christoffel／Ricci，證 Schwarzschild 真空解 | 長線，開工前先探路 |
| ER-5 | 一般的拓撲審查定理、可穿越蟲洞、ER=EPR 本身 | 不做（不在數學範圍內） |

天花板：「黑洞微觀 Gibbs 熵 = 熱力學熵」這個等號無法形式化。字典表兩欄都有機器檢查，中間的等號留白並寫明原因。

## 11. 補缺口（2026-10-23）

T2d、u⊗ū 引理、錯振幅負控制（取代 R4）、環狀 D² 緊度、轉置不是完全正，五項都完成，細節見 EVIDENCE。

剩下沒做的：
- 一般圖張量網路的「∀ 割」版本。
- 環狀熵上界的緊度。
- ER-4。

## 12. Opus 5.5 代工批次（2026-10-23）

主線（Fable 5.1）分析後派 Opus 5.5 實作、主線驗收。三項全完成：
- A 環狀熵緊度：`vnEntropy_cut_ringBellN = 2 log 2`。
- B 衛生：全庫 `set_option` 清零（改用 `omit … in` 與縮小的 `variable`），`node_run.sh` 改讀 `node.env.lean-node`。
- C 一般圖「∀割」秩上界：`TensorNetwork.lean`，主定理第 2 輪過，未觸發停損。

D4 那一行的「一般圖版延後」到此兌現。剩：n 格點路徑保真、最小割推論、ER-4、公開。

## 13. CHAIN_DESIGN 的 B0＋B1（2026-10-24）

Opus 5.5 實作、主線驗收。B0：ER-3 改名實（`UnitConeAngle`、真錐見證）、T2d 標明不依賴 β、`first_law` 的 S + c 負控制、T1∘T2 組合。B1：`NoGo.lean` 不可能定理（Gibbs 熵對 β 不增 vs β²/16π 遞增）、單點負控制（IVT）、`Chain.lean` 的耦合版。全庫 146 條。

未做（B0 範圍內但這次沒排）：ρ + ρ² 的「比值 → 1 但非 C¹」反例、`cutSize`／`minArea` 符號拆開。下一批：B2 KMS 線。

## 14. CHAIN_DESIGN 的 B2 KMS 線（2026-10-24）

Opus 5.5 實作、主線驗收。S1 歐氏準備（兩條證明互驗）、S2 KMS 逆向唯一（比規格強：不需 Hermitian、不需非空）、S3 滿秩純化唯一、S4 KMSPair 最小結構＋`tracial_iff_period`＋Gibbs 實例＋不同構定理。全庫 187 條。未做：`tfd_two_point`、KMSPair 的 α 與 σ。下一批：B3 或 B4。

## 15. CHAIN_DESIGN 的 B3＋B4（2026-10-24）

Opus 5.5 實作、主線驗收。B3：K1（含曲線層級 `kruskal_pullback`）、K1′（`inversion_swaps_UV`）、K2、K4 全做完，沒有降級。B4：G6、G5 MMI 完整版、GHZ 違反、G1、G2、G4 全做完。全庫 271 條（268 條標準三公理，3 條 `decide` 證的不依賴任何公理）。CHAIN_DESIGN 的有內容項目到此全部落地；剩 B5 可選與 X₁′、S5。（2026-10-24 更正：271 是 `Axioms.lean` 印出的條數，不是原始碼裡 `theorem` 宣告的總數；當時實為 341 條，另 70 條輔助引理沒印。見 §16。）

## 16. 收尾衛生＋S5 便宜半段（2026-10-24）

主線（Opus 5.5）直接做、直接驗。
- S5 便宜半段（`NoGo.lean` 檔尾）：`energyMean`、`trace_gibbs_mul_self`、`hasDerivAt_energyMean`（dE/dβ = −Var）、`gibbs_dS_eq_beta_dE`、`gibbs_entropy_energy_slope`。Klein 那一半沒做。
- 耦合檢驗機械化：`ErEpr/Coupling.lean`。依賴閉包＝從定理出發，遞迴展開型別與證明體裡用到的 `ErEpr.*` 常數（mathlib 不展開）。根檔 import 它，所以斷言隨 `lake build --wfail` 一起檢查。
  - 第一版用 `ConstantInfo.value?` 取證明體，對定理取不到（靜默回 `none`），閉包不展開：所有 `#assert_uses` 紅、所有 `#assert_not_uses` **假綠**。改成直接對 `ConstantInfo` 分情形取值；並加空洞守門（閉包裡沒有其他定理就判紅）。這兩件事各有一份演習（CP3、CP4）。
  - 機械檢查抓到一條原先看原始碼說錯的依賴：`ghz4_not_minCut` 不經過 `ghz4_mmi_fails`，兩者平行，共用 `regionEntropy_ghz`。已改斷言並加反向斷言。
- 反向演習一鍵重跑：`tools/drills_extract.py`（從歷史證據目錄與其基準副本逐行比對，抽出改動與反例區塊）→ `tools/drills_finalize.py`（手挑必須紅的宣告、重新指定 R17、加 BASE／S5／CP1–CP4）→ `tools/drills_manifest.json` → `tools/drills.py`。
  - R17 重新指定：原目標 `Tendsto … (𝓝 1) ↔ β = 8πM` 在 B0 改寫成 `UnitConeAngle M β ↔ β = 8πM` 後，與 COUPLE 是同一處；R17 改打 `conicalRatio_tendsto` 的極限值。
- 定理索引 `docs/THEOREM_INDEX.md`（`tools/gen_index.py`）。產生時發現 341＋4 條 `theorem` 宣告裡有 70 條沒被 `Axioms.lean` 印過；已全部補印（用 `ErEpr.` 全名，避免 `open ErEpr` 下撞名）。

## 17. S5 的 Klein 那一半（2026-10-24）

主線（Opus 5.5）直接做、直接驗，節點三輪編綠（rw 方向、轉型、`haveI` 風格各一次）。新檔 `ErEpr/Klein.lean`，22 條定理。
- 路線照 CHAIN_DESIGN §5.2：雙隨機矩陣 M_ij = |(VᴴU)_ij|²＋逐項 g(p, q) = p log p − p log q − (p − q) ≥ 0。沒有用 mathlib 的 `klFun`，直接用 `Real.log_le_sub_one_of_pos`／`log_lt_sub_one_of_pos`。
- 等號情形比規格多走一步：由「W_ij ≠ 0 ⇒ p_i = q_j」得 diag(p)·W = W·diag(q)，再推 σ = gibbs H β。
- 負控制照規格（H2、|0⟩⟨0|），另加一個「別的溫度的 Gibbs 態」，顯示等號同時釘住 β。
- 使用者同時傳來「物質－能量－信息」三圓圖；分析與可加的磚寫在 `docs/TRIANGLE.md`（未開工）。

## 18. 三角的便宜磚 T-a、T-b、T-e（2026-10-24）

使用者同意 `docs/TRIANGLE.md` §5 的建議順序。主線直接做，節點兩輪編綠（第一輪只錯在 `norm_num` 先展開 `H2`，`gibbs_H2_log2` 套不上）。新檔 `ErEpr/Triangle.lean`，10 條定理；每塊都有負控制或演習。T-c、T-d 未做。

## 19. T-c 模哈密頓量與相對熵（2026-10-24）

使用者同意做 T-c。主線直接做，節點三輪編綠（`log_div` 要先展開 `bw`；`diagonal_add` 是逐點 lambda 形式，與 Pi 加法要靠一個定義相等的 `have` 轉接；`<;>` 多餘被 linter 擋）。新檔 `ErEpr/Modular.lean`，13 條定理。
- 設計選擇：模哈密頓量由**任意**么正對角化 (U, q) 給出（`modHamOf`），不綁死 ρ₀ 的固有分解。這樣 U = 1 的對角例子可以直接算（古典 KL、不滿秩負控制），不必碰 `eigenvalues` 的抽象排序；標準形 `modHam` 再用固有分解接回去。
- 代價：不同對角化給出同一個 K 未證（需要 Hermitian 的 exp 反函數唯一）。

## 20. 糾纏第一定律，對易情形（2026-10-24）

使用者指定「先做對易（對角）情形」。主線直接做，節點三輪編綠（section 變數要 `omit`、`omit` 不能放在 docstring 後、`congr_deriv` 的目標要用 `refine` 讓目標決定）。新檔 `ErEpr/FirstLaw.lean`，11 條定理。
- 兩條路：直接微分（negMulLog 的導數、`Σv = 0` 消去 −1 項）；極小值論證（T-c 的 D ≥ 0、D(ρ₀) = 0、`IsLocalMin.hasDerivAt_eq_zero`）。耦合斷言確認第二條路完全不用第一條路的導數計算。
- 演習 FL1–FL3 都附「改壞後為假」的反例；FL2、FL3 的反例用第一條路的定理，等於兩條路互相把關。
- 不對易的情形（一般擾動）沒做：需要熵沿矩陣路徑的導數，也就是固有值的一階微擾理論。

## 21. 不對易的糾纏第一定律（2026-10-24）

使用者先要求評估「固有值微擾要多少功夫」再決定。評估結論：mathlib 沒有固有值導數、矩陣函數導數、固有值連續性；改走夾擠路線，完全繞開微擾。核心不等式 D ≤ tr((σ−ρ₀)²)/q_min 先在 numpy 上驗過（3000 組隨機不對易例子零違反，中央差分驗證第一定律誤差隨 h² 下降）。使用者回「尋找看看影子的存在性」，照路線 C 兩階段做完。
- 節點兩輪編綠（第一輪：`(t : ℂ)` 的型別標註把綁定變數推成複數、`field_simp` 已收掉目標、`convert` 鑽進 instance、隱式參數未指定、simp 參數多餘）。新檔 `ErEpr/FirstLawGeneral.lean`，20 條定理。
- 原本評估最可能卡關的「路徑在小 t 時半正定」，改用 Loewner 序拆成兩個么正共軛的實對角矩陣相加，沒有碰複數二次型。
- 演習 FG1–FG4；FG3 的反例用極小值那條路駁倒改壞的夾擠那條路。

## 22. X₁′ 類比重力的核心定理（2026-10-24）

使用者指定做 X₁′。先探 mathlib：只有實數速率的 Gamma 積分（`integral_cpow_mul_exp_neg_mul_Ioi`），Bogoliubov 係數需要的複數速率版本沒有；但有參數積分微分、解析函數唯一性定理。主線直接做。
- `ErEpr/GammaRotation.lean`（6 條）：複數速率的 Gamma 積分，兩輪編綠（`.neg` 產生 Pi 形式、`∀ᵐ t` 的 t 被 `(t : ℂ)` 推成複數、`tendsto_const_nhds` 型別不定）。這原本評估是 X₁′ 最重的一塊。
- `ErEpr/Unruh.lean`（11 條）：熱分佈、表面重力、係數比與極限、負控制，六輪編綠。其中一輪 linter 指出正則化係數比根本不需要 k > 0，照實拿掉，定理變一般。
- 防空洞：熱分佈用獨立的 Boltzmann 平均定義，不是用係數比定義（CHAIN_DESIGN §10 指出的空洞形狀）；耦合斷言機械確認。CHAIN_DESIGN 原建議用 `IsKMS` 寫熱態，但 `IsKMS` 是有限維矩陣，諧振子是無限維，改用平均佔據數，這是偏離設計稿的地方。
- 沒做：從模態內積推出 |α|² − |β|² = 1（仍是假設）；黑洞版（有位勢、灰體因子）；KMS 的無限維版本。


## 23. T-d 完整 Landauer（2026-10-24）

使用者先要求評估「熵的次可加性要多少功夫」，評估後選「兩段一起做」。評估時預估 450–650 行、15–30 輪；實際 481 行（含說明文字）、兩輪編綠（第一輪全是 linter：未用的 section 變數、`tendsto_finset_sum` 改名、多餘 simp 參數，加上一個 2×2 矩陣乘法被 simp 化成 `ᵥ*` 沒算完）。新檔 `ErEpr/Landauer.lean`，36 條定理。
- 評估時列的三個風險點：ι × κ 上兩組固有分解的 Kronecker 記帳（`kronecker_spectral` 一次 `rw` 鏈解決）、A 側部分跡恆等式（`trace_ptrA_mul`，用 `Fintype.sum_eq_single` 消掉 δ）、ε → 0 的極限（改用數列 ε = 1/(n+1) 與 `ge_of_tendsto`，逐項極限只需要 `log` 在正數處的連續性）。三處都沒有卡。
- 次可加性的設計決定：不證一般的「相對熵對參考態的下半連續性」，而是讓擾動參考態與邊際態**共用固有基底**，上界於是是有限個初等函數的和。這是評估時就選定的路線，照做。
- 防空洞：見證 `landauer_swap_witness` 讓系統熵嚴格減少，排除「定理只在 ΔS_sys ≤ 0 時成立」的空洞讀法；負控制 `negctrl_landauer_not_unitary` 說明么正性是必要的。
- 沒做：等號情形（準靜態極限）；Reeb–Wolf 的有限尺寸加強版；系統自身的哈密頓量與做功。

## 24. 糾纏的起點（2026-10-24）

使用者在 T-d 收尾後指定：相關（糾纏）起點的 Landauer 負控制，加上 Bell 態的 S(AB) = 0 < S(A)，用同一個解糾纏的么正矩陣。新檔 `ErEpr/Correlated.lean`，24 條定理，兩輪編綠（第一輪：多餘 simp 參數、一個 `omit` 省掉了實際用到的 `DecidableEq`）。
- 設計決定：解糾纏矩陣寫成 D = K/√2，K 是 Bell 基底的整數矩陣（對稱、K² = 2）。所有逐格計算都在整數矩陣 K 上做，√2 只在最後以 (1/√2)² = 1/2 出現一次，避開 16 格×16 項帶根號的 simp。
- 熱庫取 H = 0：任何溫度的 Gibbs 態都是最大混合態，Bell 態的熱庫一側恰好就是它（`ptrA_bell_eq_gibbs`）。所以負控制改變的**只有**「起點有沒有相關」，邊際態、哈密頓量、溫度都不變（`correlation_is_fuel` 把兩邊並排寫）。代價是熱恆為 0，負控制的內容全在系統熵能不能降；這點寫進範圍。
- 防空洞：耦合斷言確認負控制**不經** `landauer` 與次可加性（反例是獨立算出來的）；S(Bell) = 0 走解糾纏矩陣，**不經**秩上界；古典對照不經 Bell 也不經次可加性。
- 沒做：相關起點的一般修正（Landauer 減去互資訊）；條件熵的一般下界 −log d。

## 25. 觀測＝把線轉給儀器（2026-10-24）

起點是使用者的直覺：「沒被觀測時線條綁在一起，被觀測時線條脫落」。主線先拆成兩半回覆：「脫落的是因果的線」與不可通訊衝突；「只看系統時相關的線看起來脫落、整體其實還在」就是退相干，可以證。使用者指定做後一半：CNOT 當測量、系統干涉項歸零、熵 0 → ln 2、整體仍是純態、只動一端解不開、要兩端一起的 D 才解得開。新檔 `ErEpr/Measurement.lean`，19 條定理，兩輪編綠（第一輪：`Kraus` 沒有 import、多餘 simp 參數）。
- 設計決定：|+⟩⟨+| 的元素都是 1/2、CNOT 是 0/1 矩陣，全程不碰 √2；測量後的態正好是前一批的 Bell 態，直接沿用 D 與 S(Bell) = 0。
- 交叉檢查：整體熵的兩個 0 走兩條獨立的路（測量前：|+⟩⟨+| 寫成 (2×1)(1×2)，用 S(AB) = S(BA) 換成 1×1；測量後：解糾纏矩陣）。耦合斷言確認前者不經 Bell。
- 「只動儀器解不開」直接用既有的 `Kraus.no_signalling`：任何 Kraus 通道都不改變系統的約化態。這同時回答了「因果的線有沒有被剪」：沒有。
- 只動系統的那條（`ptrB_local_conj`）原本是在 Fin 2 上逐格算的；2026-10-25 推廣到任意維度（§29）。
- 沒做：多個儀器 qubit（環境）時的退相干速率；指針基底的選擇（einselection）；任何詮釋層面的陳述。

## 26. 糾纏的一夫一妻（2026-10-24）

使用者先要求評估「半正定矩陣那一步要多少功夫」：mathlib 有 `trace_mul_conjTranspose_self_eq_zero_iff`、`PosSemidef.trace_eq_zero_iff`、`dotProduct_mulVec_zero_iff`，ρ = BᴴB 的分解要走 C*-代數的 scoped 實例，所以改用本庫的固有分解自造 B = √D·Uᴴ。評估 250–300 行、3–6 輪；實際新檔 `ErEpr/Monogamy.lean`，16 條定理，兩輪編綠（第一輪只有一個未用的 section 變數）。
- 設計決定：純態寫成 c·|v⟩⟨v|（c·⟨v, v⟩ = 1），正好是本庫 `maxEnt` 的形式，Bell 實例不必碰 √2。
- 新的三方記帳 `ptrMid`（跡掉中間的 B），保真引理 `ptrMid_kronecker3` 確認跡掉的是中間那一個。
- 防空洞：耦合斷言確認主定理**不經** Klein 與相對熵（這是純線性代數的事實），負控制**不經**主定理與半正定那一步。
- 沒做：量化的一夫一妻（CKW 不等式、squashed entanglement）；混合邊際時的一般上界。

## 27. 糾纏交換（2026-10-24）

起點是使用者的問題「是不是因為曾經相交過一點才能連在一起」。先評估：mathlib 有 `mul_vecMulVec`、`vecMulVec_mul`、`submatrix_mul_equiv`、`kronecker_assoc`；核心計算放在向量層（Π|ψ⟩），避開 16×16 的逐格矩陣乘積。評估 280–380 行、3–6 輪；使用者選全套（含四結果平均）。新檔 `ErEpr/Swapping.lean`，28 條定理，三輪編綠：第一輪有求和次序、`Fin 2` 的 `1 + 1` 沒被化簡、一個 64 格的引理超出 heartbeat；第二輪加 `fin_two_one_add_one` 後只剩那個超時；第三輪先證 `swapVec` 是實數向量（star 不動它），再把 64 格拆成四個 16 格的引理。
- 設計偏離評估：評估時打算用指標重排從秩一投影引理推出 Π 是投影；實作時 Π 直接用條件式寫成矩陣，而且整個論證只用到 Π|ψ⟩ 與 ⟨ψ|Π 兩個向量，沒有用到 Π² = Π，所以當時沒有證「Π 是投影」（2026-10-25 補上，§29）。
- 記憶體：這個檔單獨用 `lean -M 8192` 編時峰值約 6.9 GB，在乾淨 lake build 裡那一步是 7.3 GB，是全庫最重的一個；之後若再加同規模的逐格計算，要先拆檔。
- 防空洞：四結果平均那條**不經**交換定理（各自算）；負控制**不經** Bell 投影。
- 沒做：Π 是投影的證明（2026-10-25 補上，§29）；一般的 LOCC 不可造糾纏；「接蟲洞」的任何幾何陳述。

## 28. 洞的形狀：AMPS 矛盾與不可能定理的負控制（2026-10-25）

使用者在收斂階段要求補「洞的形狀」兩塊，先評估再動手；評估 200–290 行、2–4 輪，實際兩塊第一輪就編綠。都加在既有模組，沒有開新模組。
- AMPS（`Swapping.lean`，13 條）：新的部分跡 `ptrFirst`（跡掉三方的第一個，保真 `ptrFirst_kronecker3`）；主定理是一夫一妻的直接推論。防空洞：兩個見證證明兩個要求各自都能滿足（`amps_each_half_satisfiable`，B–R 那個用 `Equiv.prodAssoc` 重排指標）；GHZ 負控制說明純態假設拿不掉。限定：原始 AMPS 用強次可加性；這裡是理想化的「恰好純態」版本。
- 不可能定理的負控制（`NoGo.lean`，6 條）：任何滿秩分佈都是 `H = diag(−log p / β)` 的 Gibbs 態（T-c 的模哈密頓量除以 β），兩段分佈 `(1 − q, q/(n+1), …)` 的熵對 q 連續，中間值定理挑出熵恰好的 q。不需要 Gibbs 熵對 β 的連續性或極限。耦合斷言確認它**不經**不可能定理的單調性證明。
- 新的對照定理 `nogo_hinges_on_fixed_hamiltonian` 把兩者並排：同一個維度、同一段 β，`∃H ∀β` 為假、`∀β ∃H` 為真。

## 29. 補兩個缺口：Π 是投影、只動系統的引理推廣到任意維度（2026-10-25）

使用者指定補 §25、§27 自己列出的兩個缺口。都改在既有模組，沒有開新模組。
- 只動系統（`Measurement.lean`）：`ptrB_local_conj` 從 Fin 2 的逐格計算改成任意有限維 ι、κ 的證明（展開成四重和、交換求和次序）；下游三條（`local_cannot_undo`、`joint_undo`、負控制）不必改。第一輪就編綠。
- Π 是投影（`Swapping.lean`，9 條）：照 §27 評估時原本的打算，用指標重排 `swapReindex : ((a, b), (c, d)) ↦ ((a, d), (b, c))` 把 Π_st 寫成 1_{AD} ⊗ |β_st⟩⟨β_st|_{BC}（`swapProj_eq_reindex`），再套一夫一妻那裡的 `rankOne_mul_self`、`rankOne_conjTranspose`。完備性 Σ Π_st = 1 先在 B、C 上證 Σ |β_st⟩⟨β_st| = 1（`sum_bellProjBC`，逐格），再整體重排。兩輪編綠：第一輪 `sum_swapProj` 想用 `submatrix_add`、`kronecker_add` 改寫和，但這兩條是兩項相加的引理、不吃 Finset 的和，改成先證一條明確的等式再逐格比。
- 防空洞：耦合斷言確認 Π² = Π **走重排與秩一投影**，**不經**核心一行 `swapProj_mulVec` 與交換定理；所以交換定理與投影性質是兩條互不依賴的證明。
- 新演習 SWP1（B、C 上的投影少了 1/2，附 P² = 2P 的反例）、LOC1（約化公式把 U 與 Uᴴ 對調）。
- 沒做：一般維度的 Bell 測量（d 維最大糾纏基底）；Π 的完備性沒有拿來改寫 `swap_average_no_signalling`（那條仍是四個結果各自算再加總）。

## 30. 面積律：熵版的 ∀ 割上界（2026-10-25）

起點是使用者的直覺「一切都往下掉，代表會拉扯時空與相關性」。主線把它接到 Jacobson（1995）與 Faulkner 等（2014）那條鏈：等效原理 → 局部視界的 Unruh 溫度 → 熵與面積成正比 → 第一定律 → 愛因斯坦方程。本庫已有 Unruh、第一定律、S = A/4（假設）三環；缺「熵 ∝ 面積」與愛因斯坦方程。後者要偽黎曼幾何，mathlib 沒有，不做；前者做得到，使用者同意「補完這一塊就停數學、轉去準備公開」。
- 先查已有的：一維（開邊界、環狀 MPS）的熵版上界與等號見證早就在 `Entropy.lean`（T3a、T3b）。這次新增的是**任意圖、任意頂點子集**的版本，加在 `TensorNetwork.lean`（改成 import `Entropy`），沒開新模組。
- 主定理 `cutEntropy_tnAmp_le` 是兩條既有定理的接合：S ≤ log 秩、秩 ≤ D^{割邊數}。新定義 `cutEntropy`（不另外歸一化，歸一化寫成假設）。
- 等號見證：k 條平行邊連兩個頂點，頂點張量把 k 隻物理腳複製到 k 條鍵上，振幅是 c·[x₀ = x₁]。共用引理 `cutEntropy_diag`：這種振幅的切口矩陣是 c 乘上重排過的單位矩陣，約化態是最大混合態，熵 log(dim)。等號見證與負控制都用它，所以都**不經**上界（耦合斷言確認）。
- 負控制：`negctrl_nonlocal_tensor` 那個非局域網路，振幅也是 [x₀ = x₁]，歸一之後熵 log 2，割邊數卻是 0。同一個共用引理一次算出兩邊。
- 兩輪編綠：第一輪只缺 `open scoped ComplexOrder`（半正定要 ℂ 的半序）和一個 `haveI` 改 `have`。
- 新演習 AL1（拿掉割邊數那個因子，附兩條割邊的反例）、AL2（拿掉歸一化）。
- 沒做：下界、最小割＝熵（RT 的等號）、隨機張量網路；任何幾何或愛因斯坦方程的陳述。

