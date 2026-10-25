# ER=EPR 玩具零件庫：總覽（2026-10-24）

整個庫的地圖、誠實範圍與上游對照。每一段都接得到定理名；細節在 `README.md`、`docs/READING_GUIDE.md`、`EVIDENCE.md`。

## 0. 一句話

這是一個 Lean 4 ＋ mathlib 的庫，把 ER=EPR 兩側能寫成數學的零件，逐一證成有限維的定理。中間那一欄（ER=EPR 本身）**刻意留白**：我們沒有去填它，而是證明它**不能是什麼**、**被哪些條件包圍**。

它**不是**：ER=EPR 的證明或反駁；新的物理或新的數學（內容幾乎都是有限維教科書事實）；任何關於 Einstein 方程、RT 公式或黑洞內部的陳述。

## 1. 數字

| 項目 | 數字 |
|---|---|
| 模組 | 26 個內容模組（另有耦合檢查、公理清單兩個檔），共 8,935 行 |
| 定理 | 599 條，全部只用標準公理（595 條用到 propext、Classical.choice、Quot.sound 三條；1 條只用 propext；3 條零公理）；沒有 `axiom`、沒有 `sorry` |
| 反向演習 | 95 份：故意改壞，確認證明會紅；大部分附「改壞後的陳述為假」的反例 |
| 耦合斷言 | 91 條：機械確認「這條用到那條」或「兩條路互不依賴」 |
| 驗證 | 每批都在節點上乾淨重建（`lake build --wfail`）並收回收據；公開版的 `evidence/` 保留每次重建的收據與演習報告 |

## 2. 地圖

### 2.1 EPR 側（量子資訊）

| 模組 | 一句話 | 不能說的 |
|---|---|---|
| `Basic`、`NoSignalling` | 部分跡的保真；對一端做任何保跡操作，另一端的約化態不變 | 只用到保跡，不刻畫完全正性 |
| `TFD` | 熱場雙態：兩側約化態都是 Gibbs 態；boost 不變 | 有限維 |
| `MPS`、`TensorNetwork` | 切口的秩 ≤ D^{割邊數}；一般圖的「∀割」上界；**面積律**：糾纏熵 ≤ 割邊數 × log D，等號對每個割邊數都達得到 | 只有上界的玩具版，不是 RT 公式 |
| `Entropy` | von Neumann 熵；S ≤ log rank；純態 S(A) = S(B) | — |
| `MinCut` | 割函數次模、MMI；GHZ 違反 MMI，所以「圖熵」是量子熵的真子集 | 推不出強次可加性 |
| `Klein`、`Modular` | Gibbs 變分原理 S ≤ βE + log Z（等號只在 Gibbs）；相對熵 ≥ 0；模哈密頓量 | 只到 ΔS ≤ Δ⟨K⟩，不證 Bekenstein 界 |
| `FirstLaw`、`FirstLawGeneral` | 糾纏第一定律 δS = δ⟨K⟩，對易與不對易兩版，夾擠證出可微 | 一階、直線路徑；沒有 Einstein 方程 |
| `Landauer` | 完整 Landauer：抹一個位元至少放 T ln 2 的熱；含一般次可加性 | 乘積起點、Gibbs 熱庫；沒有等號情形 |
| `Correlated` | Bell 態條件熵為負；起點有糾纏時 Landauer 失敗 | 只有一個 2×2 例子 |
| `Measurement` | CNOT 當測量：系統干涉項歸零、熵 0→ln 2，整體仍是純態；只動一端解不開（「只動系統」的約化公式對任何維度成立） | 退相干玩具；不談詮釋 |
| `Monogamy` | AB 的邊際是純態 ⇒ 與 C 完全不相關 | 不是量化的一夫一妻（CKW） |
| `Swapping` | 糾纏交換：沒碰過面的 A、D 接成 Bell；四個結果平均起來 A–D 沒變（不能傳訊息）；Bell 測量的四個 Π 是完整的投影測量（Π² = Π、自伴、加起來是 1）。同一個檔也有 **AMPS 防火牆矛盾**：A–B 是 Bell 時 B–R 的互資訊必為 0，兩個要求不能同時成立 | 四個 qubit、投影＋事後挑選；AMPS 是「恰好純態」的理想化版本，不是原始的強次可加性論證 |

### 2.2 ER 側（幾何）

| 模組 | 一句話 | 不能說的 |
|---|---|---|
| `ER`、`Charts` | Kruskal 時空兩個外區沒有因果曲線相連（不可穿越）；喉部面積 ≥ 16πM²；三張座標圖與反演 U↔V | 全在顯式座標裡算；mathlib 沒有偽黎曼幾何 |
| `Hawking` | 錐角條件 ⇔ β = 8πM；由第一定律得 S = A/4 | 第一定律是**假設** |
| `GammaRotation`、`Unruh` | 複數速率的 Gamma 積分；Bogoliubov 係數比 → e^{−πΩ}；熱分佈；表面重力給出同一個 β | \|α\|² − \|β\|² = 1 是假設；1+1 維、單一模態 |

### 2.3 中間：洞的形狀

| 模組 | 一句話 |
|---|---|
| `NoGo` | **不可能定理**：任何固定的有限維 H，其 Gibbs 熵都不能在一段 β 區間上等於黑洞的 β²/16π（前者對 β 不增，後者嚴格遞增）。單一 β 點永遠對得上，所以單點相等沒有內容；而讓 H 隨 β 變，同一個維度就能讓整段 β 都對上（`nogo_hinges_on_fixed_hamiltonian`：∃H ∀β 為假、∀β ∃H 為真），所以內容全在「H 固定」 |
| `KMS`、`KMSPair` | 兩側共享一套最小公理（KMS 結構）；幾何側的 β 被釘死、量子側不一定；兩側**不同構**（矩陣代數到交換環沒有保單位的環同態） |
| `Chain` | 不可能定理接上 ER 側的錨點（耦合版） |
| `Triangle` | 物質–能量–信息三角：黑洞同時填滿 Bekenstein 界與打平 Landauer（在第一定律的假設下，是代數驗算） |

## 3. 上游對照（2026-10-24 查）

查的對象：
- **Physlib**（[leanprover-community/physlib](https://github.com/leanprover-community/physlib)，commit `a6395db`）。它在 2026 年 3 月由 PhysLean 和 Lean-QuantumInfo 合併而成（[Reservoir 說明](https://reservoir.lean-lang.org/@Timeroot/quantumInfo)）。
- **Lean-Quantum**（[Hayata-Yamasaki-Group/lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum)，commit `bf1c4f6`；論文 [arXiv:2607.05492](https://arxiv.org/abs/2607.05492)）。
- **mathlib**（本庫用的 `0df444a`）。

方法：淺層 clone 後按名字與關鍵字搜，再讀相關檔的宣告。**這不是逐行比對**：Physlib 有 1,485 個 Lean 檔，名字不同的同一件事可能漏掉。

| 主題 | 上游狀態 | 判斷 |
|---|---|---|
| von Neumann 熵、S ≤ log d、純態熵 0 | Physlib 有（`Sᵥₙ`、`Sᵥₙ_le_log_d`、`Sᵥₙ_of_pure_zero`） | 重疊。本庫的定義不同（特徵多項式的根），上界是 log rank，比 log d 細 |
| 純態 S(A) = S(B)、最大糾纏態的邊際 | Physlib 有（`Sᵥₙ_of_partial_eq`、`traceRight_pure_MES`、`EoF_of_MES`） | 重疊 |
| 次可加性 | Physlib 有（`Sᵥₙ_subadditivity`，由強次可加性推出） | 重疊。本庫走另一條初等路線（擾動參考態），互相獨立 |
| **強次可加性**、Araki–Lieb、弱單調、條件互資訊 ≥ 0 | Physlib 已證完（`Sᵥₙ_strong_subadditivity` 等，沒有 `sorry`） | 本庫沒有，而且不必再做 |
| 相對熵 ≥ 0、DPI | Physlib 與 Lean-Quantum 都有（含 sandwiched Rényi 與 Umegaki） | 重疊且上游更強 |
| 部分跡的對偶刻畫 | Physlib 有（`inner_kron_one_eq_inner_traceRight`） | 重疊 |
| 熵的張量積可加 S(ρ⊗σ) = S(ρ) + S(σ) | 按名字沒找到（相對熵的可加有） | 可能是小缺口，要再確認 |
| 正則系綜：S = βU + log Z、dU/dβ = −Var、熱容量 | Physlib 有，但是**古典**（相空間測度）版本 | 同形不同物件。本庫是矩陣（量子 Gibbs 態）版 |
| Gibbs 變分原理（S ≤ βE + log Z，等號只在 Gibbs） | 按名字沒找到 | 實質是「相對熵 ≥ 0」的特例，上游等於已有內容 |
| 不可能定理、KMS 共享結構與不同構 | 沒找到 | 本庫獨有 |
| Landauer、糾纏第一定律、模哈密頓量 | 沒找到 | 本庫獨有（但都是已知物理） |
| 一夫一妻（純態邊際）、糾纏交換、CNOT 退相干、不可通訊（具名定理） | 沒找到（Physlib 有 CNOT 閘與 pinching 通道，沒有這些陳述） | 本庫獨有，但都很初等 |
| MPS、張量網路秩上界、最小割與 MMI | 沒找到 | 本庫獨有 |
| Kruskal、Hawking、Unruh、Bogoliubov、TFD | 沒找到（Physlib 只有 Schwarzschild 內部解的不可壓縮球） | 本庫獨有；一次網路搜尋也沒找到別人在定理證明器裡做黑洞熱力學或 ER=EPR |
| 複數速率的 Gamma 積分 | mathlib 只有實數速率（`integral_cpow_mul_exp_neg_mul_Ioi`） | **真的是 mathlib 的缺口**，而且是純分析、適合送上游 |

## 4. 這代表什麼

**不能說的：**
- 「首次形式化次可加性」。Physlib 已有，連強次可加性都證完了。
- 「首次形式化 von Neumann 熵」或「相對熵非負」。上游都有。

**可以說的（照實、加限定）：**
- ER 側（Kruskal 不可穿越、Hawking 錐角、Unruh 熱分佈）與中間的不可能定理、KMS 共享結構，**在我們查得到的範圍內**上游沒有。
- 驗證方法：反向演習（附反例）＋機械耦合斷言＋每批乾淨重建。這套做法本身就是可帶走的東西。

**上游的成本：** 本庫用的是裸的 `Matrix`，Physlib 用 `MState`／`HermitianMat`／`CPTPMap`，送進去要改寫成他們的 API，不是複製貼上。說明文字是中文，也要改。

## 5. 接下來

- **送上游**：最合適的是**複數速率的 Gamma 積分**送 mathlib（mathlib 確實沒有、純分析、約 150 行、和物理無關），補丁在 `upstream/mathlib-gamma-complex-rate/`。其他量子資訊零件上游已有更一般的版本。
- **數學停在這裡**：強次可加性不必做（Physlib 有）。之後若再加，只挑上游沒有、又能說明 ER=EPR 那個洞的東西。
- **勘誤**：發現錯誤或說過頭的地方，請在 GitHub 開 issue。

## 6. 讀的順序

0. 想先從直覺讀：`docs/QUESTIONS.md`（十三個問題，每題接到對應的定理）。
1. `docs/READING_GUIDE.md`：三種「等號」、把洞逼到角落的策略。
2. 這份總覽的第 2 節地圖。
3. 想看某一塊怎麼證，就到 `README.md` 找那一節，再到 `EVIDENCE.md` 看它的演習與收據。
