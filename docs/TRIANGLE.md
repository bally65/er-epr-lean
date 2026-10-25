# 物質、能量、信息三角，與本庫怎麼對接

2026-10-24。起因：使用者傳來一張三圓文氏圖。三個圓是物質、能量、信息，三條邊各標一個公式：

| 邊 | 圖上的公式 | 名字 |
|---|---|---|
| 物質 ↔ 能量 | `E = mc²` | 質能等價 |
| 能量 ↔ 信息 | `Q ≥ k_B T ln 2` | Landauer 原理：抹掉 1 位元，至少要放出這麼多熱 |
| 物質 ↔ 信息 | `I ≤ 2πcRm / (ħ ln 2)` | Bekenstein 界：半徑 R、質量 m 的系統最多裝這麼多位元（`E = mc²` 代進 `S ≤ 2πkRE/(ħc)`） |

這份文件回答三件事：
1. 三條邊是不是同一種「關係」？
2. 正中間白色那一塊是什麼？
3. 本庫已經有哪些定理接得上，還能加哪些磚？

文中自然單位 `G = c = ħ = k_B = 1`，只有在講圖上的公式時才寫回單位。

---

## 1. 三條邊不是同一種「關係」

照 `docs/READING_GUIDE.md` §1 的「三種等號」分類：

- **`E = mc²` 是等式，而且是物理定律**（狹義相對論的結論）。在本庫裡它不是定理，是**輸入**：ER 側從頭到尾用同一個 `M` 同時當質量和能量（`first_law_area` 的說明文字寫明「假設：能量就是質量 `E = M`」）。Lean 不會「證明」`E = mc²`，就像不會證明單位換算。
- **Landauer 和 Bekenstein 是不等式（界）**，不是等式。它們說的是「最多」或「至少」，平常的系統離界很遠。

所以三條邊裡有兩條是同一類（界），一條是另一類（等同）。把三者畫成對稱的三角形，會讓人以為它們地位相同；其實「信息」那個圓的兩條邊都是不等式。

## 2. 數學上，兩個界是同一個不等式

兩個界的現代證明，核心都是同一件事：**相對熵非負**。寫成本庫剛證完的形式就是 Klein 不等式（`ErEpr/Klein.lean`）：

> 對任何密度矩陣 σ：S(σ) ≤ β·tr(σH) + log Z，等號只在 σ = Gibbs 態。
> 等價寫法：ΔS ≤ β·ΔE，其中 Δ 是 σ 相對於 Gibbs 態的差。

- **Landauer**（Reeb–Wolf 2014 的證法）：系統和一個溫度 T 的熱庫一起做么正演化，熱庫一開始是 Gibbs 態。熱庫的熵增加 ΔS_R 不超過 β·（熱庫吸收的熱 Q），這一步**就是** Klein 套在熱庫上。再配上熵的次可加性，就得到「系統少了 ΔS 的熵，熱庫至少吸收 T·ΔS 的熱」；ΔS = ln 2（一個位元）時就是 `Q ≥ k_B T ln 2`。
- **Bekenstein**（Casini 2008 的證法）：把真空限制在一個區域上，它的約化態是 Gibbs 態，「哈密頓量」是模哈密頓量 K（Rindler 楔裡 K = 2π × boost 生成元）。對任何激發態，ΔS ≤ Δ⟨K⟩，**這也是** Klein（β = 1、H = K）。再用場論把 Δ⟨K⟩ 估成 ≤ 2πRE，才得到圖上的形式。

所以「能量 ↔ 信息」和「物質 ↔ 信息」兩條邊，底下是同一個定理換兩種參考態：熱庫的 Gibbs 態，和真空的模態。這是這張圖最值得整合的地方。

**限定**：Klein 只給出「ΔS ≤ βΔE」這一半。Landauer 還需要次可加性（2026-10-24 已補上，見 §5 的 T-d）；Bekenstein 還需要「K 是 boost 生成元」與「⟨K⟩ ≤ 2πRE」，兩者都是量子場論的內容，本庫做不到。Bekenstein 界原本的形式有已知爭議（物種數問題等），Casini 的相對熵版本才是精確的陳述。

## 3. 正中間白色那一塊：黑洞

三條同時**取等號**的物體，就是黑洞。以 Schwarzschild 黑洞（質量 M，視界半徑 R = 2M）驗算：

- **物質 ↔ 能量**：E = M（`E = mc²`，c = 1）。
- **物質 ↔ 信息**：Bekenstein 界的右邊 2πRE = 2π·2M·M = 4πM²，正好是 Bekenstein–Hawking 熵 S = A/4 = 4πM²。**黑洞剛好填滿 Bekenstein 界**。寫回單位：圖上的 `2πcRm/(ħ ln 2)` 代 R = 2Gm/c²，得 4πGm²/(ħc ln 2)，等於 S_BH/(k_B ln 2)。
- **能量 ↔ 信息**：第一定律 dS/dE = β = 1/T。丟一個位元進黑洞，熵增加 ln 2，質量（能量）就增加 T·ln 2，正好是 Landauer 的下限 `k_B T ln 2`。**黑洞是剛好打平 Landauer 的熱庫**。

為什麼是黑洞？因為三個等號的條件都是「態是熱的（Gibbs／KMS）」：Klein 的等號只在 Gibbs 態成立（`vnEntropy_eq_beta_energy_add_log_iff`）；Landauer 的等號要準靜態，也就是每一步都是 Gibbs 態；Hartle–Hawking 態在視界外是 Hawking 溫度的 KMS 態。本庫的 KMS 線（`isKMS_unique`）和 Klein 的等號情形講的是同一件事：**熱態是唯一取等號的態**。

## 4. 本庫已經有的零件

| 圖上的位置 | 本庫的定理 | 身分 |
|---|---|---|
| 能量 ↔ 信息（核心不等式） | `vnEntropy_le_beta_energy_add_log`（Klein） | 定理 |
| 等號只在熱態 | `vnEntropy_eq_beta_energy_add_log_iff`、`isKMS_unique` | 定理 |
| β = 熵對能量的斜率（EPR 側） | `gibbs_dS_eq_beta_dE`、`gibbs_entropy_energy_slope` | 定理 |
| β = 熵對能量的斜率（ER 側） | `first_law_area` 的假設 `hS` | 假設 |
| 黑洞溫度 | `hawking_beta`（β = 8πM，在單位錐角條件下） | 定理（條件版） |
| 黑洞熵 = 面積/4 | `first_law_area`（S = 4πM² = A/4）、`throat_area_eq`（A = 16πM²） | 定理（假設第一定律） |
| 物質 ↔ 能量 | 全庫用同一個 M 當質量與能量 | 輸入，不是定理 |

## 5. 可以加的磚（由便宜到貴）

| 編號 | 內容 | 成本 | 誠實程度 |
|---|---|---|---|
| T-a | **黑洞填滿 Bekenstein 界**：R = 2M、E = M 時 2πRE = 4πM² = A/4（接 `throat_area_eq`、`first_law_area`） | 易（10–20 行，純代數） | 只是代數恆等式；「R 取視界的面積半徑」是約定 |
| T-b | **熱庫那一半的 Landauer**：熱庫從 Gibbs 態變到任何態 ρ′，ΔS_R ≤ β·ΔE_R，等號只在 ρ′ 仍是同溫 Gibbs 態 | 易（由 Klein＋等號情形，約 20 行） | 有限維、精確；但還不是完整的 Landauer |
| T-c | **有限維的 Casini 形式**：任何滿秩參考態 ρ₀ 都可以寫成 Gibbs 態（K = −log ρ₀），所以 ΔS ≤ Δ⟨K⟩ | 中（要把 Klein 推廣到一般滿秩參考態，約 60–100 行） | 只到「ΔS ≤ Δ⟨K⟩」；K 與 2πRE 的關係做不到 |
| T-d | **完整 Landauer（Reeb–Wolf 形式）**：系統＋熱庫＋么正演化 ⇒ β·Q ≥ ΔS_系統 | 難（要熵的次可加性與張量積的熵可加性，約 250–400 行，高風險） | 有限維、精確 |
| T-e | **黑洞打平 Landauer**：第一定律下，熵增加 ln 2 時能量恰好增加 T·ln 2 | 易（`first_law_area` 的直接推論） | 繼承 `first_law_area` 的假設 |

建議順序：T-a、T-b、T-e 一批（都便宜，而且剛好把文氏圖正中間那塊在本庫裡標出來），再看要不要往 T-c、T-d 走。

**2026-10-24：T-a、T-b、T-e 已做完**（`ErEpr/Triangle.lean`，在 lean-node 編過）：

| 編號 | 定理 | 負控制 |
|---|---|---|
| T-a | `bekensteinBound_throat`：喉部面積半徑 r(M/2) = 2M、E = M 時 2πRE = A/4；`first_law_saturates_bekenstein`：滿足 `first_law_area` 假設的熵函數恰好等於這個界 | `negctrl_bekenstein_isotropic_radius`：誤用各向同性座標 ρ = M/2 當半徑，只得 A/16 |
| T-b | `reservoir_entropy_le_beta_heat`：熱庫從 Gibbs 態變到任何態，ΔS ≤ β·ΔE；`reservoir_entropy_eq_beta_heat_iff`：等號只在終態仍是同溫 Gibbs 態；`landauer_reservoir_bit`：熵至少增加 ln 2 時吸收的能量至少 ln 2/β | `negctrl_reservoir_not_gibbs`：熱庫起點不是同溫 Gibbs 態時，不等式失敗（H2 上熵不變而能量減少 1/3） |
| T-e | `hasDerivAt_bh_energy_of_entropy`：沿 S = 4πM²，dE/dS = 1/(8πM)；`bh_landauer_saturated`：單位錐角條件下 dE/dS = 1/β = T | 演習 TE1（8πM 改 4πM） |

**2026-10-24：T-c 也做完**（`ErEpr/Modular.lean`）：

- 任何滿秩參考態 ρ₀ = U·diag(q)·Uᴴ 都是自己的模哈密頓量 K = U·diag(−log q)·Uᴴ 在 β = 1 的 Gibbs 態（`exp_neg_modHamOf`、`gibbs_modHamOf`，配分函數 = 1）。所以 T-c 直接沿用 T-b：`entropy_le_modular`：ΔS ≤ Δ⟨K⟩，等號只在 σ = ρ₀（`entropy_eq_modular_iff`）；標準形 `entropy_le_modHam` 只要 ρ₀ 正定。
- 相對熵 D(σ‖ρ₀) = tr(σK) − S(σ)（`relEntropyOf`）：D ≥ 0、D = 0 ⇔ σ = ρ₀；對角時恰好是古典 KL 散度 Σ p(log p − log q)（`relEntropyOf_diagonal`）。這就是 §2 一直說的「相對熵 ≥ 0」，現在是本庫的定理。
- 保真：Gibbs 參考態的模哈密頓量是 βH + log Z（`modHamOf_gibbs`），所以 T-c 在 Gibbs 參考態上退化回 T-b。
- 負控制 `negctrl_modular_not_fullRank`：參考態不滿秩（q = (1, 0)）時，Lean 的 log 0 = 0 讓 K = 0，不等式對最大混合態失敗。
- 限定：只到 ΔS ≤ Δ⟨K⟩。「真空的模哈密頓量是 2π × boost 生成元」（Bisognano–Wichmann）與「Δ⟨K⟩ ≤ 2πRE」是量子場論的內容，本庫沒有，所以仍然**沒有**證 Bekenstein 界。K 依賴所選的對角化；「Hermitian 的 exp 反函數唯一」未證。

**再往下一步：糾纏第一定律**（`ErEpr/FirstLaw.lean`，對易情形）。T-c 的不等式 ΔS ≤ Δ⟨K⟩ 在參考態附近的一階是等號：δS = δ⟨K⟩（`entanglement_first_law_diag`）。第二條證明只用「相對熵在 ρ₀ 取極小值 0」（`first_law_of_relEntropy_min`），不碰任何導數的值。物理上，這個一階等號加上 RT 公式（面積 = 熵）就是 Faulkner 等人（2014）推出線性化 Einstein 方程的輸入；後一半本庫沒有。

**不對易情形與影子的存在性**（`ErEpr/FirstLawGeneral.lean`）。一般擾動（不必與參考態對易）也有 δS = δ⟨K⟩，而且先證了熵沿路徑**可微**。證法沒有用固有值微擾：相對熵被夾在 0 與 C·t² 之間（下界是 Klein，上界是新證的 D(σ) ≤ tr((σ − ρ₀)²)/c），所以一階項只能是 tr(δρ·K)。參考態不滿秩時熵在 0 不可微：影子只在滿秩參考態上存在。

**2026-10-24：T-d 完整 Landauer 也做完**（`ErEpr/Landauer.lean`）。系統 ρ_S 與 Gibbs 熱庫 γ 一起做任意么正演化 U：

> S(ρ_S) − S(ρ′_S) ≤ β·(tr(ρ′_R H) − tr(γH))（`landauer`）

抹掉一個位元至少放 T ln 2 的熱（`landauer_bit`）；熱庫不吸熱，系統的熵就不會減少（`no_heatless_erasure`）。證明是 Reeb–Wolf 的四塊：么正不變（既有）、張量積可加 `vnEntropy_kronecker`、次可加性 `vnEntropy_subadditive`、熱庫那一半（T-b）。

- 次可加性原本是最大的風險：標準證法 D(ρ_AB‖ρ_A⊗ρ_B) ≥ 0 要參考態滿秩，但抹除之後邊際態恰好不滿秩。繞法是參考態改用 (1−ε)ρ_A + ε/d（`mixUnif`），它和 ρ_A 共用固有基底，所以上界只是有限個初等函數的和，ε → 0 的極限逐項可算（a_i = 0 的項恆為 0）。整個證明不需要固有值對矩陣的連續性。
- 乘積參考態的模哈密頓量是 K_A ⊗ 1 + 1 ⊗ K_B（`modHamOf_kronecker`），配上部分跡的對偶刻畫，相對熵拆成兩個邊際各自的項（`vnEntropy_le_marginal_cross`）。為此補了 A 側部分跡的對偶刻畫（`trace_ptrA_mul`）。
- 見證：最大混合 qubit 與 β = ln 2 的熱庫交換之後，系統熵嚴格減少、熱庫嚴格吸熱 1/6（`landauer_swap_witness`），所以定理不是空話。
- 負控制：換成非么正的重置 |0⟩⟨0| + |0⟩⟨1|，熱庫完全不吸熱就把最大混合態變成純態（`negctrl_landauer_not_unitary`）：么正性不能拿掉。跡不為 1 時次可加性可以失敗（`negctrl_subadditive_unnormalized`）。
- 限定：有限維；熱庫起點恰為 Gibbs 態、系統與熱庫起點是乘積態；「熱」定義為熱庫的能量增量，系統的哈密頓量與做功沒有出現在定理裡。等號情形（準靜態）沒有刻畫。
- **乘積起點拿不掉**（`ErEpr/Correlated.lean`）：熱庫取 H = 0、邊際態不變，只把起點從乘積態換成 Bell 態，一個解糾纏的么正矩陣就能讓系統的熵少 ln 2 而熱是 0（`negctrl_landauer_correlated`、`correlation_is_fuel`）。同一個矩陣也證了 Bell 態 S(AB) = 0 < S(A) = ln 2（條件熵為負）。這是 EPR 那一側的資源（糾纏）在熱力學裡出現的地方：del Rio 等（Nature 2011）稱之為負的抹除成本。本庫只有這個 2×2 例子，沒有一般的修正公式。

耦合斷言（`ErEpr/Coupling.lean`）把 §2、§3 的分工機械化：T-b **用到** Klein、**不碰** ER 側；T-a、T-e **用到** `first_law_area`／`hawking_beta`、**不經** Klein。所以「黑洞同時填滿兩個界」在本庫裡是 ER 側的代數與微分，不是 Klein 推出來的。完整 Landauer 用到 Klein 兩次：熱庫那一半直接用（T-b），次可加性經相對熵用（T-c）；耦合斷言確認次可加性那條路**不**經 T-b，張量積可加性**不**經 Klein。Bekenstein 那一邊仍只到 ΔS ≤ Δ⟨K⟩。

## 6. 不做、也不該說的

- 不說「本庫統一了物質、能量與信息」。三條邊的身分不同（§1），兩個界只共用一個數學核心（§2），而且 Bekenstein 那一邊的物理（場論的模哈密頓量、Δ⟨K⟩ ≤ 2πRE）不在本庫；Landauer 只有有限維、乘積起點、Gibbs 熱庫的版本。
- 不說「本庫證明了 Bekenstein 界」。T-c 最多到 ΔS ≤ Δ⟨K⟩。
- 黑洞填滿兩個界（§3）在本庫裡只能是代數驗算，前提是第一定律與 β = 8πM，這兩者在 ER 側分別是假設與條件版定理。

## 參考（作者、年份、刊物；DOI 未逐一核對）

- R. Landauer, IBM J. Res. Dev. 5, 183 (1961)。
- J. D. Bekenstein, Phys. Rev. D 23, 287 (1981)。
- H. Casini, Class. Quantum Grav. 25, 205021 (2008)：相對熵版的 Bekenstein 界。
- D. Reeb, M. M. Wolf, New J. Phys. 16, 103011 (2014)：以相對熵證 Landauer，含有限尺寸修正。
- A. Bérut 等, Nature 483, 187 (2012)：Landauer 界的實驗（先前對話已查過）。
