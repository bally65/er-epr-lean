# ER=EPR toy pieces in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23642750.svg)](https://doi.org/10.5281/zenodo.23642750)

A Lean 4 + mathlib library that proves, in finite dimensions, the pieces on each side of
the ER=EPR conjecture, and leaves the conjecture itself as an explicit gap. Instead of
trying to fill the gap, it proves what the gap cannot be and which conditions surround it.

**What is proved**
- EPR side: no-signalling, thermofield-double states, von Neumann entropy facts, a full
  Landauer bound, monogamy for pure marginals, entanglement swapping, and an area law
  for tensor networks (entropy ≤ number of cut edges × log D, tight for every count).
- ER side: Kruskal non-traversability, β = 8πM from the cone-angle condition, and the
  Unruh/Bogoliubov thermal ratio.
- The middle: no fixed finite-dimensional Hamiltonian has Gibbs entropy equal to
  β²/16π on an interval of β, and this hinges exactly on the Hamiltonian being fixed;
  an idealized (pure-state) AMPS contradiction; graph-realizable entropies form a strict
  subset of quantum entropies (four-party GHZ violates MMI).

**What it is not**
- Not a proof or a refutation of ER=EPR.
- Not new physics: most items are textbook finite-dimensional facts, and several already
  exist upstream in more general form (e.g. Physlib).
- No statement about Einstein's equations, the Ryu–Takayanagi formula, or black-hole
  interiors. Some results rest on stated assumptions (for example, S = A/4 assumes the
  first law).

**How it is checked**
599 theorems, all depending only on `propext`, `Classical.choice`, `Quot.sound`; no
`sorry`, no `axiom`. 95 reverse drills (each deliberately breaks a statement and checks
that the proof turns red, most with a counterexample showing the broken statement is
false). 91 machine-checked coupling assertions ("this proof uses that lemma" / "these two
proofs are independent", `ErEpr/Coupling.lean`). A clean `lake build --wfail` on every
batch; this public copy keeps the build receipts and drill reports in `evidence/`.
No human expert has reviewed the library yet.

**Build**

```
lake exe cache get
lake build
```

Lean `v4.33.1`, mathlib `0df444a`. The largest module (`ErEpr.Swapping`) peaks at about
7.4 GB of memory. The scripts in `tools/` drive the author's private build node and are
not needed to build.

**Reading order**: `docs/QUESTIONS.md` (thirteen intuitive questions mapped to theorems),
`docs/OVERVIEW.md` (the map and an upstream comparison), `docs/READING_GUIDE.md`.
Documentation is in Traditional Chinese; theorem names and statements are in Lean.

**AI disclosure**

I chose the direction of this library, which results to prove, and whether to take each
next step; many of the topics came from my own intuitive questions about physics, such as
measurement, entanglement swapping, and the other side of a black hole. The Lean code, the
proofs, and most of the documentation were written by an AI (Anthropic's Claude) under my
direction. Every theorem is checked by the Lean kernel and depends only on the three standard
axioms; reverse drills (deliberately breaking a statement and confirming that the proof fails)
and coupling assertions check that the proofs do not take shortcuts. These are mathematical
results: they show what holds, and what cannot hold, under the stated definitions and
assumptions. Whether nature actually works this way is a question for experiment; this library
neither proposes nor performs any experiment. No physicist or mathematician has reviewed it
yet; if you find an error or an overstatement, please open an issue.

*(English translation assisted by Claude. The original, in the author's words:)*

> 這個庫的方向、要證明哪些東西、每一步要不要做，都是我決定的；很多題目來自我自己對物理的直覺提問，例如觀測、糾纏交換、黑洞的另一邊。Lean 程式碼、證明和大部分文件，是 AI（Anthropic 的 Claude）在我的指示下寫的。每一條定理都經過 Lean 核心的機器檢查，只用到標準的三條公理；另外用反向演習（故意改壞、確認會失敗）和耦合斷言，檢查證明沒有走捷徑。這些都是數學上的結果：它們說明在給定的定義與假設下，哪些事成立、哪些不可能。自然界是不是真的這樣運作，需要實驗來回答；這個庫本身沒有提出、也沒有做任何實驗。目前還沒有物理或數學專家審過，如果發現錯誤或說過頭的地方，歡迎開 issue。

**How to cite** (see `CITATION.cff`):

```
Li, Wei-Ting. er_epr_lean: Machine-checked finite-dimensional pieces around the
ER=EPR conjecture in Lean 4. Zenodo, 2026. DOI: 10.5281/zenodo.23642750
(version v0.1.0: 10.5281/zenodo.23642751)
```

```bibtex
@software{li_er_epr_lean_2026,
  author    = {Li, Wei-Ting},
  title     = {{er\_epr\_lean}: Machine-checked finite-dimensional pieces around the {ER=EPR} conjecture in {Lean} 4},
  year      = {2026},
  publisher = {Zenodo},
  version   = {v0.1.0},
  doi       = {10.5281/zenodo.23642751},
  url       = {https://doi.org/10.5281/zenodo.23642751}
}
```

**License**: Apache-2.0 (see `LICENSE`). Copyright 2026 Li Wei-Ting.
Errors and questions: please open a GitHub issue.

---

# er_epr_lean

ER=EPR 字典兩側的玩具零件，用 Lean 4／mathlib 形式化：
- **EPR 側**：在有限維複矩陣上做。
- **ER 側**：在顯式座標下的度規係數上做。

## 已完成（2026-10-23）

**第一批：Basic＋T1 不可通訊。** 已在 lean-node 上編譯，公理只有標準三條。證據見 `EVIDENCE.md`。

- `ErEpr/Basic.lean`：
  - 定義：部分跡 `ptrB`／`ptrA`、區塊 `blk`、`id ⊗ Φ`（`idKron`）。
  - 保真引理 F1–F8：對偶刻畫、乘積態、保跡、保半正定、Bell 見證、Tr_A≠Tr_B 見證、乘積保真、唯一性。
  - 純態約化 `ptrB_pure`／`ptrA_pure`。
- `ErEpr/NoSignalling.lean`：
  - 主定理 `ptrB_idKron`：B 側任何 ℂ-線性保跡映射，都不改變 A 側的約化態。
  - Kraus 推論。
  - 負控制 N1–N4。
  - 見證：Pauli X、amplitude damping、轉置。

## 範圍

ER=EPR 與 Ryu–Takayanagi 是量子重力的物理猜想，本身不是數學命題。這個庫沒有證明它們，也不聲稱驗證了它們。

ER 側只做到座標層級：度規係數是直接給定的，沒有證明它們滿足 Einstein 方程，也沒有流形上的幾何。

其他限制：
- T1 只要求保跡，所以它談的是「保跡線性映射」，不是「物理通道」。轉置保跡但不是完全正映射，它也滿足 T1；「轉置不是完全正」由 `transposeMap_not_completelyPositive` 證明（部分轉置後的 Bell 態不是半正定）。
- 本庫只證「邊際不變」，沒有證輸出仍是量子態。
- Choi–Kraus 等價沒有形式化。
- 上游已經有量子資訊的 Lean 庫，見 `DESIGN.md` §9。本庫不宣稱是第一個。

**T2 熱場雙態（`ErEpr/TFD.lean`）：已在 lean-node 編過。**
- `ptrB_tfdState`：TFD 的 A 側約化態等於 Gibbs 態。Gibbs 態用矩陣指數定義，TFD 用固有分解建構，兩者獨立定義；兩者相等由橋接引理 `tfdAmp_mul_conjTranspose` 證明。
- `ptrA_tfdState`：B 側約化態是 Gibbs 態的轉置。
- `gibbs_pauliY_ne_transpose`：σ_y 下兩側確實不同。
- `trace_tfdState`：TFD 歸一化成立。
- `gibbs_diagonal_real`：對角 H 的 Gibbs 態就是 Boltzmann 權重。
- 數值見證與負控制：diag(0,1)、β = ln 2 時 Gibbs 態是 (2/3, 1/3)；β 弄反號、振幅漏 1/2 都會得到錯的結果。

**T3 MPS 秩上界（`ErEpr/MPS.lean`）：已在 lean-node 編過。**
- `rank_cutAt_mpsOpen_le`：開邊界 MPS 在任一處切開，Schmidt 秩 ≤ D。
- `rank_cutAt_mpsRing_le`：環狀 MPS 切成兩段，Schmidt 秩 ≤ D²。
- `rank_ptrB_pure`：上述秩等於該切口 A 側約化密度矩陣的秩。
- `rank_cutAt_bell`：Bell 對的秩恰好是 2 = D，所以開邊界的上界是緊的。
- 範圍：只談秩，不談熵；這是 RT「≤」那一半的離散玩具版。上界對任何 MPS 都成立，包括與全像無關的網路，所以不稱 RT。

**第二批 von Neumann 熵（`ErEpr/Entropy.lean`）：已在 lean-node 編過。**
- 定義 `vnEntropy`：對特徵多項式的根求 −λ log λ 的和。另證它等於對固有值求和。
- 健全性：
  - `vnEntropy_diagonal`：對角矩陣的熵是 Shannon 熵。
  - `vnEntropy_maxMixed`：d 維最大混合態的熵是 log d。
- `vnEntropy_le_log_rank`：密度矩陣的熵 ≤ log rank。
  - 負控制 `negctrl_unnormalized`：拿掉歸一化，結論為假。
- `vnEntropy_ptrA_pureOf_eq`：任何純態兩側約化態的熵相等。
- `vnEntropy_ptrA_tfdState`：TFD 的 B 側是 Gibbs 態的轉置，但熵仍等於 Gibbs 態的熵。
- 歸一化 MPS 在切口的糾纏熵：
  - `vnEntropy_cut_mpsOpen_le`：開邊界 ≤ log D。
  - `vnEntropy_cut_mpsRing_le`：環狀 ≤ 2 log D。
  - `vnEntropy_cut_bellN`：歸一化 Bell 對的熵恰好是 log 2，開邊界的上界是緊的。
- 範圍：這是 RT「≤」那一半的離散玩具版，不是 RT。「TFD 糾纏熵＝熱力學熵」只是有限維矩陣上的事實，與黑洞熵的對應沒有形式化。

**ER 側 ER-1、ER-2（`ErEpr/ER.lean`）：已在 lean-node 編過。**

mathlib 沒有偽黎曼幾何，所以 ER 側都在顯式座標裡做：度規以座標下的係數給出。

- `no_causal_curve_between_exteriors`：Kruskal 座標下沒有因果曲線連通左右兩個外區，這是「橋不可穿越」的玩具版。
  - 見證 `meet_in_interior`：兩邊可以在黑洞內部相遇。
  - 見證 `bridge_slice_spacelike`：橋在空間上是連著的。
  - 負控制 `negctrl_spacelike_connects`：只拿掉「因果」條件，結論就失敗。
- `throat_area_le`、`throat_area_eq`：Einstein–Rosen 橋的喉部是面積 16πM² 的極小球面。
- `inversion_isometry`：反演 ρ ↦ M²/4ρ 保持度規係數，並交換兩個漸近端。
- 範圍：只用到度規係數的形式，沒有證明它們滿足 Einstein 方程，也不是一般的拓撲審查定理。

**ER-3 與收尾（`ErEpr/Hawking.lean`）：已在 lean-node 編過。**
- `hawking_beta`：歐氏視界沒有錐狀奇點，若且唯若 β = 8πM。
  - 「沒有錐狀奇點」定義成「τ 圓周長 ÷（2π × 固有距離）」的極限為 1。
  - 保真引理 `properDist_r_hasDerivAt`：固有距離確實滿足 dρ/dr = 1/√F。
  - 負控制 `negctrl_wrong_beta`：β = 4πM 時這個極限是 1/2。
- `first_law_area`：若熵滿足 S(0) = 0、dS/dm = β(m)，而且每個質量的 β 都讓視界光滑，則 S = 4πM² = A/4。
  - A 是 ER-2 的喉部面積。
  - 這條定理假設了 E = M、第一定律，以及 T = 1/β。它是座標層級的一致性檢查，不是推導。
  - 見證 `first_law_witness`：這些假設能同時成立。

## 兩欄字典表

| 字典的一行 | ER 側（座標） | EPR 側（矩陣） | 中間的等號 |
|---|---|---|---|
| 不能傳訊 | `no_causal_curve_between_exteriors` | `ptrB_idKron`（T1） | 類比，未形式化 |
| 兩側互換 | `inversion_isometry`；在 Kruskal 座標下反演就是 U ↔ V（`inversion_swaps_UV`） | `ptrA_tfdState`（B 側是轉置） | 類比，未形式化 |
| 溫度 | `hawking_beta`：單位錐角條件（一階、必要）⇔ β = 8πM | `ptrB_tfdState`（TFD 在 β 下的約化態是 Gibbs 態） | 「永恆黑洞 = TFD(β_H)」是物理假設，未形式化；這一行的等號是**單向特化**（ER 決定 β，EPR 吃進去），見 `docs/CHAIN_DESIGN.md` §3.3 |
| 熵 | `first_law_area`（S = A/4 = 4πM²） | `vnEntropy_ptrA_tfdState`（TFD 糾纏熵 = Gibbs 熵） | 「Gibbs 熵 = 黑洞熱力學熵」需要量子重力，**無法形式化** |
| 面積與糾纏上界 | `throat_area_eq`（A = 16πM²） | `vnEntropy_cut_mpsOpen_le`（≤ \|γ\| log D） | RT 的等號未證明 |
| **不可能定理** | S_BH(β) = β²/16π 隨 β 嚴格遞增（比熱為負） | 任何有限維 H 的 Gibbs 熵隨 β 不增：dS/dβ = −β·Var(H) | `no_finite_dim_gibbs_matches_bh`：兩者在任何正長度 β 區間上不可能相等。這把中間那欄的洞釘死：「黑洞 = 固定有限維正則系綜」一開始就排除。單點相等調得到、沒有內容（`negctrl_single_point`）。反過來，只要讓 H 隨 β 變，同一個維度就能讓整段 β 都恰好對上 β²/16π（`negctrl_nogo_varying_hamiltonian`）：不可能定理的內容全在「H 固定」，差別只在量詞順序（`nogo_hinges_on_fixed_hamiltonian`：∃H ∀β 為假、∀β ∃H 為真）。限定：只對漸近平坦黑洞；AdS 大黑洞比熱為正不適用；不是對 ER=EPR 的反駁 |

兩欄都有機器檢查，中間那一欄就是 ER=EPR 本身。它不是數學命題，本庫刻意留白。

## 接下來

**補上的缺口（2026-10-23）：**
- `tfd_boost_invariant`（T2d）：(H⊗1 − 1⊗Hᵀ)\|TFD⟩ = 0。**不依賴 β**：它等價於振幅與 H 交換（`boost_invariant_iff_commute`），Bell 振幅也滿足（`boost_invariant_one`），所以不能當溫度那一行的連結。
- `vecOf_tfdAmp`：TFD 振幅攤平後是 Σ e^{−βE/2} u_n ⊗ ū_n。
- `negctrl_wrong_amplitude`：右側少了共軛的錯誤 TFD 照樣通過 T2a，但在 σ_y 下違反 T2b。這條正面證明取代了原本只是「證明跑不過」的 R4 演習。
- `rank_cutAt_ringBell`：環狀 MPS 的秩恰為 D² = 4，所以 T3b 的上界是緊的。
- `transposeMap_not_completelyPositive`：轉置不是完全正映射。

**一般圖張量網路（`ErEpr/TensorNetwork.lean`）：已在 lean-node 編過。**
- `rank_cutMat_tnAmp_le`：任意有限圖、任意頂點子集 W，切口矩陣的秩 ≤ D^(割邊數)，割邊＝恰有一端在 W 的邊。
- 頂點張量依型別只看得見入射邊上的鍵。拿掉這個限制，上界就不成立（`negctrl_nonlocal_tensor`：一條只接在頂點 0 的自環，割邊數 0，秩卻是 2）。這是定理的實質內容所在。
- 保真：兩格點的路徑等於 `mpsOpen`（`tnAmp_path2TN`），兩格點的環等於 `mpsRing`（`tnAmp_ring2TN`）。
- 緊度：割 1 條邊秩恰為 2（`rank_cutMat_bellTN`），割 2 條邊秩恰為 4（`rank_cutMat_ringBellTN`）。
- 環狀熵也補了緊度：`vnEntropy_cut_ringBellN` = 2 log 2。
- **面積律（熵版，2026-10-25）**：歸一化之後，任意圖、任意頂點子集 W 的糾纏熵 ≤ 割邊數 × log D（`cutEntropy_tnAmp_le`；一維特例是上面的 T3a、T3b 熵版）。等號達得到：k 條平行邊、任何 k 與 D，熵恰為 k log D（`area_law_saturated`，直接算成最大混合態，耦合斷言確認不經上界）。負控制：非局域網路歸一之後割邊數 0、熵卻是 log 2（`negctrl_nonlocal_entropy`）。
- 範圍：秩與熵都只有上界（RT「≤」那一半）；W 任意、不必連通；「對所有分割取最小割」沒有寫成定理；不是 RT。

**B0 修正與 B1 不可能定理（`ErEpr/NoGo.lean`、`ErEpr/Chain.lean`；2026-10-24，照 `docs/CHAIN_DESIGN.md` §4、§2）：已在 lean-node 編過。**
- ER-3 改名實：`UnitConeAngle` 是「單位錐角條件」，一階、必要；`coneAngleRatio_cone` 證錐角 2πc 的真錐比值恰為 c，c ≠ 1 就不滿足。充分性（笛卡兒圖下度規分量光滑）本庫未證。
- `negctrl_first_law_const`：`first_law_area` 的 S(0) = 0 不能拿掉，S + c 滿足其餘假設而結論為假。
- `ptrB_idKron_tfdState`（T1∘T2）：對 TFD 的 B 側施任何保跡映射，A 側仍是 Gibbs 態。
- 不可能定理：`antitoneOn_gibbsEntropyFn`（Gibbs 熵對 β 不增）、`hasDerivAt_gibbsEntropyFn`（dS/dβ = −β·Var）、`energyVar_nonneg`、`no_finite_dim_gibbs_matches_bh`、質量參數版 `_mass`，以及接上 ER 錨點的耦合版 `no_gibbs_matches_first_law`（真的用到 `hawking_beta` 與 `first_law_area`）。
- 健全性：β = 0 時熵 = log d（`vnEntropy_gibbs_zero`），並由此得 S ≤ log d，與既有 `vnEntropy_le_log_rank` 交叉一致。

**B2 KMS 線（`ErEpr/KMS.lean`、`ErEpr/KMSPair.lean`、`TFD.lean` 增補；2026-10-24，照 `docs/CHAIN_DESIGN.md` §5.2、§3）：已在 lean-node 編過。**
- `tfdAmp_eq_exp`：TFD 振幅就是歐氏演化 e^{−(β/2)H}；另有不經固有分解的第二條證明互驗。
- `isKMS_unique`：跡為 1 且滿足 KMS 條件 tr(σ·a·e^{−βH} b e^{βH}) = tr(σ·b·a) 的矩陣只有 gibbs H β。這讓 β 從「Gibbs 的參數」變成「被 KMS 條件唯一刻畫的參數」。負控制：最大混合態不滿足 KMS。
- `tfd_ptrB_isKMS`／`tfd_ptrA_isKMS`：TFD 的 A 側是 H 的 KMS 態，B 側是 Hᵀ 的 KMS 態。
- `purification_unique_of_isUnit`：滿秩方陣的純化唯一到一個 B 側么正；推論 `tfdAmpWrong_eq`：錯誤振幅 = 正確振幅 × (UUᵀ)，這就是 T2a 看不見、T2b 才釘住的那個么正。一般 Uhlmann 不做（mathlib 無極分解）。
- `KMSPair`：只含態 ω、虛時一步 ν、非退化性、KMS 條件的最小結構（CHAIN_DESIGN §3.2 的 reduct，沒有流 α 與對合 σ）。`tracial_iff_period`：ω tracial ⇔ ν 是恆等。`ofComm`：交換代數上 ν 必為恆等。Gibbs 實例 `gibbsKMSPair`；`gibbs_tracial_iff_scalar`：Gibbs 態 tracial ⇔ e^{−βH} 是純量。所以「溫度」那一行是單向特化：幾何側（交換）剛性，量子側自由。
- `no_ringHom_matrix_to_comm`：M₂(ℂ) 到任何非平凡交換環沒有保 1 環同態，兩側不同構。

**B3 ER 側接縫（`ErEpr/Charts.lean`；2026-10-24，照 `docs/CHAIN_DESIGN.md` §5.1）：已在 lean-node 編過。**
- K1：同一個 Schwarzschild 的三張圖由係數恆等式接起來（`FK_mul_kf`、`FK_mul_deriv_sqrt_kf`、`confIso_eq_rOfRho`），不用 Lambert W。曲線層級 `kruskal_pullback`：Kruskal 度規沿右外區曲線拉回成 Schwarzschild 度規。ER-1 的抽象 F 從此和 ER-2、ER-3 共用同一個物件。
- K1′：喉部切片的顯式映射 `sliceX`；`inversion_swaps_UV`：ER-2 的反演 ρ ↦ M²/4ρ 在 Kruskal 座標下就是 U ↔ V。
- K2：boost 保因果向量與三個區域（`futureCausal_boost`、`boost_preserves_prod`）；負控制 `negctrl_boost_spacelike`：類空向量 boost 後「指向未來」會翻掉。這是 T2d 在幾何側的對應，但仍是類比。
- K4：喉部在切片上是極小、在整個時空裡是鞍點（`area_slice_gt`、`area_timelike_lt`、`r_eq_at_bifurcation`）。

**B4 圖對態的約束（`ErEpr/MinCut.lean`；照 §5.3）：已在 lean-node 編過。**
- G6：割函數次模性 `cutEdges_card_submodular`、`cutEdges_compl`。
- G5：最小割函數滿足 MMI（`minCut_mmi`）：mc(A)+mc(B)+mc(C)+mc(ABC) ≤ mc(AB)+mc(BC)+mc(AC)，證法是逐頂點的三位元收縮映射，64 種情形 `decide`。
- 四方 GHZ 的量子熵**違反** MMI（`ghz4_mmi_fails`：3 log 2 < 4 log 2），所以沒有任何圖、任何比例常數的最小割能重現它（`ghz4_not_minCut`）。圖可實現的熵嚴格小於量子熵：這是幾何對態的最小可證約束，不是 RT。
- G1、G2：秩 ≤ 1 ⇔ 外積（`rank_le_one_iff_vecMulVec`）、割邊 0 ⇒ 乘積態（`tnAmp_product_of_no_cut`）；負控制 `negctrl_product_with_bond`：有鍵但張量秩 1，振幅仍是乘積，「連通 ⇒ 糾纏」為假。
- G4：`cutLeft` 單射且 `cutRight` 滿射 ⇒ 秩恰為 D^{割邊數}（`rank_cutMat_eq_of_inj_surj`）。

**S5 便宜半段與收尾衛生（2026-10-24）：已在 lean-node 編過。**
- `gibbs_dS_eq_beta_dE`：Gibbs 態的 dS/dβ = β·dE/dβ（E = ⟨H⟩，`energyMean`；`hasDerivAt_energyMean`：dE/dβ = −Var）。推論 `gibbs_entropy_energy_slope`：Var ≠ 0 時 (dS/dβ)/(dE/dβ) = β，也就是 β 是熵對能量的斜率。ER 側 `first_law_area` 把同一個關係（dS/dM = β）當假設；這裡在 EPR 側它是定理。同形不同值：值對不上由不可能定理負責。
- 耦合檢驗機械化（`ErEpr/Coupling.lean`，隨 `lake build` 一起跑）：`#assert_uses` 檢查依賴閉包含指定錨點、`#assert_not_uses` 檢查不含；閉包裡沒有其他定理時判「不可信」而紅（防止閉包沒展開造成假綠燈）。
- 反向演習一鍵重跑：`tools/drills.py`（清單 `tools/drills_manifest.json`，由歷史證據目錄自動抽出，再補新演習），報告在 `evidence/drills_<時間>/REPORT.md`。
- 定理索引：`docs/THEOREM_INDEX.md`（`tools/gen_index.py` 從磁碟產生：位置、公理、演習、耦合斷言）。產生索引時發現原始碼裡有 70 條輔助引理沒被 `Axioms.lean` 印過公理，已全部補印。

**S5 的 Klein 那一半（`ErEpr/Klein.lean`；2026-10-24，照 `docs/CHAIN_DESIGN.md` §5.2）：已在 lean-node 編過。**
- `vnEntropy_le_beta_energy_add_log`：任何密度矩陣 σ 都滿足 S(σ) ≤ β·tr(σH) + log Z。
- `vnEntropy_eq_beta_energy_add_log_iff`：等號 ⇔ σ = gibbs H β。推論：Gibbs 態本身取等號（`vnEntropy_gibbs_eq_beta_energy_add_log`）；能量期望值相同的態裡，Gibbs 態是熵唯一的最大者（`vnEntropy_le_gibbs_of_energy_eq`、`vnEntropy_lt_gibbs_of_energy_eq`）。
- 證法不用矩陣對數：兩組固有基底的重疊 |⟨v_i, u_j⟩|² 是雙隨機矩陣，缺口恰好寫成 Σ M_ij·g(p_i, q_j)，每項由 log x ≤ x − 1 非負（`klein_gap_eq`、`kleinGap_nonneg`）。等號推出 σ 與 H 同時對角化。
- 負控制：H = diag(0, 1)、β = ln 2 時，純態 |0⟩⟨0|（`negctrl_klein_pure_H2`）與 β′ = −ln 2 的 Gibbs 態（`negctrl_klein_other_beta_H2`）都嚴格小於右邊。
- 耦合斷言：不等式**不**依賴 Gibbs 熵的閉式 `vnEntropy_gibbs_eq_fn`，只有等號方向用到它，所以 S(gibbs) = β·E + log Z 是由兩條獨立路線各得一次。
- 這個不等式是 Landauer 與（Casini 形式的）Bekenstein 兩種界共同的數學核心；兩者怎麼接、黑洞為何同時填滿兩個界，見 `docs/TRIANGLE.md`。這一節不證兩個界本身；完整 Landauer 見下面 T-d 一節，Bekenstein 界本庫沒有證。

**物質－能量－信息三角的便宜磚（`ErEpr/Triangle.lean`；2026-10-24，照 `docs/TRIANGLE.md` §5）：已在 lean-node 編過。**
- T-a 黑洞填滿 Bekenstein 界：喉部面積半徑 2M、能量 M 時 2πRE = A/4（`bekensteinBound_throat`）；接上第一定律（`first_law_saturates_bekenstein`）。只是代數恆等式，半徑取面積半徑是約定；用錯半徑只得 A/16（負控制）。
- T-b 熱庫那一半的 Landauer：熱庫從 Gibbs 態出發，ΔS ≤ β·ΔE，等號只在準靜態（`reservoir_entropy_le_beta_heat`、`_eq_beta_heat_iff`）；吸收一個位元（ln 2）的熵至少要 T ln 2 的能量（`landauer_reservoir_bit`）。起點不是 Gibbs 態時不等式會失敗（負控制）。完整 Landauer 見下面 T-d 一節。
- T-e 黑洞打平 Landauer：沿 S = 4πM²，dE/dS = 1/β = T（`bh_landauer_saturated`），一階陳述。
- 耦合斷言確認 T-b 只靠 Klein、T-a 與 T-e 只靠 ER 側。

**T-c 模哈密頓量與相對熵（`ErEpr/Modular.lean`；有限維 Casini 形式）：已在 lean-node 編過。**
- 任何滿秩參考態 ρ₀ 都是 K = −log ρ₀ 在 β = 1 的 Gibbs 態（`gibbs_modHamOf`）；於是 ΔS ≤ Δ⟨K⟩，等號只在 σ = ρ₀（`entropy_le_modular`、`entropy_eq_modular_iff`、標準形 `entropy_le_modHam`）。
- 相對熵 D(σ‖ρ₀) = tr(σK) − S(σ)：D ≥ 0、D = 0 ⇔ σ = ρ₀；對角時是古典 KL 散度（`relEntropyOf_diagonal`）。Gibbs 參考態的 K = βH + log Z（`modHamOf_gibbs`）。
- 負控制：參考態不滿秩時不等式失敗（`negctrl_modular_not_fullRank`）。
- 這只是 Casini 論證的有限維骨架；「真空的 K 是 boost 生成元」與「Δ⟨K⟩ ≤ 2πRE」是場論的內容，本庫沒有，所以沒有證 Bekenstein 界。

**糾纏第一定律，對易情形（`ErEpr/FirstLaw.lean`）：已在 lean-node 編過。**
- 參考態 ρ₀ = diag(q)、沿保跡的對角路徑 ρ(t) = diag(q + t·v)：δS = δ⟨K⟩，K = −log ρ₀（`entanglement_first_law_diag`）。
- 兩條互不依賴的證明（耦合斷言機械確認）：直接微分（`hasDerivAt_entropy_diagPath`、`hasDerivAt_modEnergy_diagPath`）；以及只用「相對熵 ≥ 0、在 ρ₀ 為 0」的極小值論證（`first_law_of_relEntropy_min`）。一階的等號是二階不等式的影子。
- 一階相等、二階嚴格：v ≠ 0、t ≠ 0 時相對熵 > 0（`relEntropy_diagPath_pos`）。
- 負控制：K 換成別的參考態的模哈密頓量，第一定律就不成立（`negctrl_first_law_wrong_reference`）。
- 範圍：只做對易情形；一般擾動見下一節。這是「從糾纏推出重力」那條路的輸入之一，但本庫沒有 RT 公式與幾何動力學，所以沒有任何關於 Einstein 方程的陳述。

**不對易的糾纏第一定律：影子的存在性（`ErEpr/FirstLawGeneral.lean`）：已在 lean-node 編過。**
- 任何 Gibbs 參考態、任何無跡 Hermitian 擾動 X（不必對易）：t ↦ S(G + tX) 在 0 **可微**，導數 β·tr(XH)（`hasDerivAt_entropy_gibbsPath`）。任何滿秩參考態 ρ₀：d/dt S(ρ₀ + tX)|₀ = tr(XK)，K = −log ρ₀（`entanglement_first_law`）。
- 不用固有值微擾，用夾擠：Klein 給下界 D ≥ 0，新證的二次上界 D(σ) ≤ tr((σ − G)²)/c（`klein_gap_le_sq`）給上界，所以 0 ≤ D(t) ≤ C·t²，可微性與導數值一起出來。另需證路徑在小 t 時仍是態（`eventually_gibbsPath_posSemidef`）。
- 第二條路：只假設可微，用極小值論證得出同一個導數（`first_law_gibbs_of_hasDerivAt`）。耦合斷言確認兩條路互不依賴，也不依賴對易版。
- 對易時退化回上一節（`first_law_general_agrees_diag`，由導數唯一性）。
- 負控制「影子不存在」：參考態不滿秩時，熵在 0 不可微（`negctrl_first_law_not_fullRank`）。

**X₁′ 類比重力的核心定理（`ErEpr/GammaRotation.lean`、`ErEpr/Unruh.lean`；照 `docs/CHAIN_DESIGN.md` §10）：已在 lean-node 編過。**
- 複數速率的 Gamma 積分（mathlib 只有實數速率）：Re a > 0、Re r > 0 ⇒ ∫₀^∞ t^{a−1}e^{−rt} dt = (1/r)^a Γ(a)（`integral_gammaKernel`）。證法：積分號下微分得到右半平面上複可微，再用解析函數的唯一性定理從正實軸延拓過去。
- Bogoliubov 係數比：重疊積分 ∫ x^{a−1}e^{−(δ∓ik)x} dx（a = ε + iΩ）的模長比恰好是 exp(−2Ω·arg(δ+ik))，與正則化參數 ε 無關（`bogoliubov_ratio_regularized`）；視界極限 δ → 0⁺ 時趨向 e^{−πΩ}（`bogoliubov_ratio_tendsto`），平方後是 e^{−2πω/κ}（`bogoliubov_ratio_sq_tendsto`）。
- 熱分佈：係數比加上玻色子的正則對易關係 |α|² − |β|² = 1，⇒ |β|² 等於逆溫度 2π/κ 的諧振子平均佔據數（`bogoliubov_thermal`）。平均佔據數獨立定義成 Boltzmann 加權平均，並證它是 Bose–Einstein 的 1/(e^{βω} − 1)（`meanOccupation_eq`）；耦合斷言確認它不經 Bogoliubov 計算。
- 兩條獨立的路，同一個溫度：Schwarzschild 的表面重力 κ = F′(2M)/2 = 1/(4M)，β = 2π/κ = 8πM，正好滿足 ER-3 的單位錐角條件（`unitConeAngle_of_surfaceGravity`）；表面重力那條路不經 `hawking_beta`。
- 負控制：對易關係寫成費米子的 |α|² + |β|² = 1 會得到 Fermi–Dirac（`negctrl_bogoliubov_fermi`）；κ → 0（沒有視界）時熱因子 → 0（`negctrl_no_horizon`）。
- 範圍：「這兩個積分就是 Bogoliubov 係數（差一個共同歸一化）」是物理設定、寫在說明文字裡；|α|² − |β|² = 1 是假設；只做 1+1 維、單一模態，沒有灰體因子。

**T-d 完整 Landauer（`ErEpr/Landauer.lean`；照 `docs/TRIANGLE.md` §5）：已在 lean-node 編過。**
- 系統 ρ_S 與 Gibbs 熱庫 γ 一起做任意么正演化：S(ρ_S) − S(ρ′_S) ≤ β·（熱庫吸收的熱）（`landauer`）。抹掉一個位元至少放 T ln 2 的熱（`landauer_bit`）；熱庫不吸熱，系統的熵就不會減少（`no_heatless_erasure`）。
- 證明的四塊：么正不變；張量積可加 S(ρ⊗σ) = S(ρ) + S(σ)（`vnEntropy_kronecker`）；次可加性 S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)，邊際態不必滿秩（`vnEntropy_subadditive`）；熱庫那一半（T-b）。
- 次可加性的繞法：參考態改用往均勻分佈混一點的 (1−ε)ρ_A + ε/d，它與 ρ_A 共用固有基底，ε → 0 的極限逐項可算。不需要固有值連續性（mathlib 沒有）。
- 見證：交換系統與熱庫時，系統熵嚴格減少、熱庫嚴格吸熱（`landauer_swap_witness`）。負控制：非么正的重置不放熱就能抹除（`negctrl_landauer_not_unitary`）；跡不為 1 時次可加性失敗（`negctrl_subadditive_unnormalized`）。
- 範圍：有限維；熱庫起點是 Gibbs 態、起點是乘積態；「熱」是熱庫的能量增量，系統的做功不在定理裡；等號情形沒有刻畫。

**糾纏的起點（`ErEpr/Correlated.lean`）：已在 lean-node 編過。** 兩件事用同一個解糾纏的么正矩陣 D（`disentangle`，D·Bell·Dᴴ = |00⟩⟨00|）證：
- Bell 態 S(AB) = 0 < S(A) = S(B) = ln 2（`vnEntropy_bell`、`vnEntropy_ptrB_bell`）：條件熵 S(AB) − S(B) = −ln 2（`bell_conditional_entropy`），互資訊 2 ln 2（`bell_mutual_information`）。古典的 S(A) ≤ S(AB) 在這裡失敗（`negctrl_entropy_monotone`）；對角（古典）聯合分佈確實滿足它（`vnEntropy_ptrB_diagonal_le`），所以失敗的原因是糾纏。
- Landauer 的乘積假設拿不掉（`correlation_is_fuel`、`negctrl_landauer_correlated`）：熱庫取 H = 0，系統與熱庫的邊際態完全相同；乘積起點時任何么正演化都不能降低系統的熵，Bell 起點時 D 一步就把系統變成純態、熱是 0。物理讀法：與熱庫的糾纏可以當抹除的燃料（del Rio 等，Nature 2011）。
- 範圍：只有一個 2×2 的例子；沒有證「相關起點時的修正項是互資訊」這類一般陳述；H = 0 讓熱恆為 0，負控制的內容全在系統的熵能不能降。

**觀測＝把線轉給儀器（`ErEpr/Measurement.lean`，退相干的最小模型）：已在 lean-node 編過。** 系統 qubit 在 |+⟩，儀器在 |0⟩，測量的交互作用是 CNOT：CNOT(|+⟩⟨+| ⊗ |0⟩⟨0|)CNOTᴴ = Bell（`cnot_measure`）。
- 只看系統，線像是脫落了：干涉項 1/2 → 0、出現機率不變（`measurement_dephases`），熵 0 → ln 2（`measurement_entropy`）。
- 整體的線還在：測量前後整體都是純態。兩個 0 由兩條獨立的路算出（測量前用秩一的 |+⟩⟨+|，測量後用解糾纏矩陣），兩者一致正是么正不變的要求（`measurement_total_entropy_conserved`）。
- 只動一端解不開：只動系統（任何么正 U ⊗ 1），熵仍是 ln 2（`local_cannot_undo`）；只動儀器（任何 Kraus 通道），系統的約化態完全不變（`pointer_cannot_undo`，就是不可通訊）。兩端一起才解得開：D 讓系統回到純態，再做一次 CNOT 則干涉項回到 1/2（`joint_undo`）。
- 負控制：交互作用只動系統（不糾纏）時，系統的熵仍是 0（`negctrl_local_no_decoherence`）：沒有糾纏就沒有退相干。
- 「只動系統」那條約化公式 Tr_B((U⊗1)X(U⊗1)ᴴ) = U·Tr_B X·Uᴴ 對任何維度都成立（`ptrB_local_conj`），不只 2×2。
- 範圍：2×2 玩具；「坍縮」在這裡只是「系統的約化態變成對角」，不談詮釋，也沒有定義觀測者；因果沒有被剪斷（只動儀器改變不了系統）。

**糾纏的一夫一妻（`ErEpr/Monogamy.lean`）：已在 lean-node 編過。**
- 三方態 ρ_ABC 若 AB 的邊際是純態 P，則整體必為 P ⊗ ρ_C（`monogamy`）。證法：R = (1−P)⊗1 是投影，tr(ρR) = tr(P(1−P)) = 0；半正定矩陣寫成 BᴴB（B = √D·Uᴴ），tr(ρR) = tr((BR)(BR)ᴴ) = 0 ⇒ ρR = 0（`mul_eq_zero_of_trace_mul_eq_zero`）；於是 ρ = (P⊗1)ρ(P⊗1) = P ⊗ X。
- A 與 C 不相關：跡掉中間的 B（`ptrMid`，保真 `ptrMid_kronecker3`）得 ρ_AC = ρ_A ⊗ ρ_C，互資訊為 0（`monogamy_mutualInfo`）。
- Bell 實例：AB 的邊際是 Bell 態時，A 與 B 的互資訊 2 ln 2（最大）、A 與 C 是 0（`bell_monogamy`）；假設可以滿足（`bell_monogamy_witness`）。
- 負控制：邊際不是純態時結論失敗（`negctrl_monogamy_mixed`）。
- 範圍：只證「邊際是純態 ⇒ 與第三方完全不相關」；量化的一夫一妻（CKW 不等式等）沒有做。防火牆悖論（AMPS 2012）用的就是這條，但本庫沒有黑洞內部或輻射的模型。

**糾纏交換（`ErEpr/Swapping.lean`）：已在 lean-node 編過。** 四個 qubit A、B、C、D，起點是兩對 Bell 態 Bell_AB ⊗ Bell_CD，A 與 D 從沒交互過。
- 交換之前，A–D 是乘積態，互資訊 0（`swap_before`）。
- 對中間的 B、C 做 Bell 投影 Φ⁺：機率 1/4，歸一化之後 A–D 恰好是 Bell 態，互資訊從 0 變成 2 ln 2（`entanglement_swapping`）。核心只有一行：Σ_{b,c}[b = c][a = b][c = d] = [a = d]（`swapProj_mulVec`）。
- 不能傳訊息：四個 Bell 結果各自機率 1/4（`swap_prob`），各自把 A–D 接成一個 Bell 態；但四者平均起來，A–D 的約化態與交換前完全相同（`swap_average_no_signalling`）。要知道「接上了」，得有人用古典通道告訴 D 結果是哪一個。
- 負控制：B、C 改成各自量到 |0⟩（不糾纏的測量），A–D 仍是乘積態（`negctrl_swap_separate`）：相交點必須是糾纏的測量。
- Π 是完整的投影測量：Π² = Π（`swapProj_mul_self`）、自伴（`swapProj_isHermitian`）、四個結果加起來是 1（`sum_swapProj`）。證法：把指標重排成 (A, D) ⊗ (B, C)，Π 就是 1 ⊗ |β_st⟩⟨β_st|（`swapProj_eq_reindex`），再用一夫一妻那裡的秩一投影引理。
- 記帳：`ptrBC` 一次跡掉中間的 B、C（保真 `ptrBC_kronecker`、`trace_ptrBC`）；互資訊 `mutualInfo`。
- 範圍：四個 qubit、一次 Bell 測量，寫成「投影＋事後挑選」；「各自量」只有一個結果，沒有證一般的 LOCC 定理；「接蟲洞」只在說明文字裡。
- **AMPS 防火牆矛盾**（同一個檔）：三方 A（內部）、B（晚期輻射）、R（早期輻射）。A–B 是 Bell 態時，B 與 R 的互資訊一定是 0（`amps_monogamy`，一夫一妻的直接推論），所以「A–B 最大糾纏」與「B–R 最大相關」不能同時成立（`amps_contradiction`）。兩個要求各自都能滿足（`amps_each_half_satisfiable`），矛盾只來自同時成立；A–B 只是古典相關（GHZ）時，B 可以同時和 R 相關（`negctrl_amps_mixed`）。範圍：原始的 AMPS 論證用強次可加性（量化版）；這裡是「恰好純態」的理想化版本。

**尚未做：**
- 一般 n 格點路徑與 `mpsOpen` 的保真（只做了兩格點）。
- KMSPair 的流 α 與對合 σ；「態決定 β」。
- Landauer 的等號情形（準靜態）與有限尺寸修正（Reeb–Wolf 的加強版）。

先看圖再看磚：`docs/READING_GUIDE.md`（三種等號、把洞逼到角落的策略，每段接對應定理名）。設計與完成判準見 `DESIGN.md`，中間一欄的拆法見 `docs/CHAIN_DESIGN.md`。

## 編譯

`lakefile.toml` 與 `lake-manifest.json` 已補上：只依賴 mathlib `0df444a`，傳遞依賴的版本照抄 `chemical_quantum` 的 manifest。根檔是 `ErEpr.lean`。

**`lake build` 已實際跑過**（lean-node；最新一次是 2026-10-24 收尾後的版本，證據在 `evidence/er_epr_20261024T063448Z_lakebuild/`）。
- 做法：在全新目錄裡解開工作樹，依 manifest 從 GitHub 抓依賴，再 `lake exe cache get`，然後逐模組 `lake build --wfail`（警告也算失敗），最後整包再跑一次。一鍵：`tools/lake_build_remote.sh`。
- 結果：15 個模組（含 `ErEpr.Coupling` 的耦合斷言）和根檔都由 lake 實際編譯，全部通過；345 條定理全部印過公理，342 條標準三公理、3 條零公理。
- manifest 在抓依賴前後、建置前後都沒被 lake 改寫，9 個套件的版本和 manifest 一致。

自己重現：

```bash
lake exe cache get
```

```bash
lake build --wfail
```

```bash
lake env lean ErEpr/Axioms.lean
```

開發時的逐檔驗證，只在 lean-node 上跑（連線位址從 `infra/remote_node/bin/node.env.lean-node` 讀，腳本裡不含位址）：

```bash
tools/node_run.sh <標籤>
```
