# 導讀：先有圖，再看磚

這個庫裡的每一條定理單獨看都很小，多半是教科書習題。有份量的不是磚，是**圖**：哪個等號能證、哪個不能、不能的那個怎麼量它的形狀。這份導讀先講圖，每一段後面接對應的定理名，讓你讀程式碼時知道那塊磚在牆上的哪個位置。

定理名都可以在 `ErEpr/*.lean` 裡直接搜尋。每條定理的證據（節點編譯收據、公理檢查、反向演習）在 `EVIDENCE.md`；為什麼這樣設計在 `DESIGN.md` 與 `docs/CHAIN_DESIGN.md`。

---

## 1. 三種「等於」

ER=EPR 這句話裡的等號，可以是三種不同的東西：

| 種類 | 意思 | 能不能證 |
|---|---|---|
| **類比** | 兩個結構形狀像 | 不能，它是修辭 |
| **同構** | 有一個明確的映射，兩邊互相翻譯，翻譯保持所有結構 | 能，而且只有這種能 |
| **物理等同** | 兩個描述指的是**同一個世界** | 不能，它是對應規則，不是數學物件之間的映射 |

Maldacena–Susskind 2013 寫的是第三種。第三種沒有「可證」的真假，只有「與世界符不符合」。這不是 Lean 的限制，紙筆也證不了；Church–Turing 論題是同一類東西。

這個庫從頭到尾只做第二種，而且老實標出每一行字典裡的等號是哪一種。

---

## 2. 策略：不填洞，把洞逼到角落，再量它的形狀

既然第三種等號不能證，方案就是：從兩端往中間推定理，推到推不動為止，剩下的那一格命名為 **h**，然後不假裝它不存在，反過來研究它：

1. 說它**不能是什麼**（§5 的不可能定理）。
2. 說任何想當 h 的東西**必須共享什麼**（§6 的 KMSPair）。

像康德談理性的界限：從外面看不到，但可以從裡面把輪廓描出來。也像否定神學：不說它是什麼，只說它不是什麼。

十個獨立角色（物理、幾何、量子統計、量子資訊、張量網路、工程、兩個懷疑者、數學結構、文獻）各自定位洞的位置，全部收斂到同一格：「這個幾何的量子態 = 某個 (H, β) 的 KMS 態」。說法不同，位置相同（`docs/CHAIN_DESIGN.md` §0）。

---

## 3. 讓「小定理」可信的四個動作

磚小，所以牆的可信度靠砌法。每一塊磚都要過四關：

**(a) 定義紀律：保真引理。** 定義寫錯了，定理照樣能編過，這是最常見的假綠燈。所以每個自家定義都附「它真的是那個東西」的引理。
- 部分跡是對的部分跡：`trace_ptrB_mul`（對偶刻畫）、`ptrB_ne_ptrA_witness`（兩側不能寫反）。
- `id ⊗ Φ` 真的是 `id ⊗ Φ`：`idKron_kronecker`（乘積態上對）、`idKron_unique`（滿足這條的線性映射只有一個，所以糾纏態上也對）。
- 固有距離真的是固有距離：`properDist_r_hasDerivAt`。

**(b) 負控制：拿掉假設，結論必須為假。** 不是「證明跑不過」，是正面證明改壞後的陳述是假的。
- 不可通訊拿掉保跡就壞：`negctrl_not_tp`；把保跡誤寫成 unital 也壞：`negctrl_unital_not_tp`。
- 「所有邊際都不變」是錯的：`negctrl_replace_changes_ptrA`；局域性不能省：`negctrl_A_side_changes_ptrB`。
- 熵 ≤ log rank 拿掉歸一化就壞：`negctrl_unnormalized`（diag(1/e, 1/e) 的熵 2/e > log 2）。
- 張量網路讓頂點偷看非入射邊就壞：`negctrl_nonlocal_tensor`。
- Hawking 溫度取一半就有錐狀奇點：`negctrl_wrong_beta`；第一定律的積分常數不能省：`negctrl_first_law_const`。
- 最大混合態不滿足 KMS：`negctrl_maxMixed_not_kms`。

**(c) 反向演習：故意改壞定義，編譯必須紅。** 每批新定理都在副本上改壞一處、送節點，記錄紅在哪一條。表在 `EVIDENCE.md`。演習只證「證明跑不過」，能不能證「改壞後為假」要另外看 (b)。全部演習（含「改壞後為假」的反例區塊）收在 `tools/drills_manifest.json`，`tools/drills.py` 一鍵重跑，報告寫在 `evidence/drills_<時間>/REPORT.md`。

**(d) 耦合檢驗：只擾動一側，定理必須斷。** 兩欄要真的接上，不是各自平行擺著。把 ER 側的 8πM 改成 4πM，`first_law_area`、`no_gibbs_matches_first_law` 都要紅（`EVIDENCE.md` 的 COUPLE 演習）。另外有一份機械檢查 `ErEpr/Coupling.lean`：把定理的證明體遞迴展開成本庫常數的依賴閉包，`#assert_uses` 要求某些錨點一定在裡面（例如 `no_gibbs_matches_first_law` 真的用到 `hawking_beta`），`#assert_not_uses` 要求某些錨點一定不在（例如不可能定理 `no_finite_dim_gibbs_matches_bh` 只靠 EPR 側）。它隨 `lake build` 一起跑，任何一條不符就編譯失敗。它第一次跑就抓到一個說錯的地方：`ghz4_not_minCut` 並不是接在 `ghz4_mmi_fails` 上，兩者是共用 `regionEntropy_ghz` 的平行證明。

---

## 4. 兩欄字典：每一行是哪種等號

| 字典的一行 | ER 側（顯式座標） | EPR 側（有限維矩陣） | 中間的等號 |
|---|---|---|---|
| 不能傳訊 | `no_causal_curve_between_exteriors`：未來因果曲線 U、V 不減，兩外區不相連。見證：兩邊能在內區相遇 `meet_in_interior`、橋在空間上連著 `bridge_slice_spacelike`；負控制：類空曲線連得通 `negctrl_spacelike_connects` | `ptrB_idKron`：B 側任何保跡線性映射不改 A 側約化態；Kraus 版 `Kraus.no_signalling`。注意：轉置保跡但不完全正，也滿足 `witness_transpose`，所以定理談的是「保跡映射」不是「物理通道」（`transposeMap_not_completelyPositive`） | **類比**。兩條定理沒有共同物件 |
| 兩側互換 | `inversion_isometry`：ρ ↦ M²/4ρ 保係數，喉部 `throat_area_eq` 是不動點；在 Kruskal 座標下反演就是 U ↔ V（`inversion_swaps_UV`） | `ptrA_tfdState`：TFD 的 B 側是 Gibbs 態的**轉置**；σ_y 下真的不同 `gibbs_pauliY_ne_transpose`、`negctrl_ptrA_ne_gibbs`；少了共軛的錯振幅騙得過 A 側騙不過 B 側 `negctrl_wrong_amplitude` | **類比** |
| 時間／boost | `futureCausal_boost`：boost 保因果向量與三區；`boost_preserves_prod`；負控制 `negctrl_boost_spacelike`（類空向量 boost 後「指向未來」會翻掉） | `tfd_boost_invariant`：(H⊗1 − 1⊗Hᵀ)\|TFD⟩ = 0。但它等價於振幅與 H 交換 `boost_invariant_iff_commute`，Bell 振幅也滿足 `boost_invariant_one`，**與 β 無關** | **類比**，而且不是溫度的連結 |
| 溫度 | `hawking_beta`：`UnitConeAngle`（單位錐角，一階、必要）⇔ β = 8πM。真錐見證 `coneAngleRatio_cone`。充分性未證；**X₁′**：表面重力 κ = 1/(4M) 給 β = 2π/κ，與錐角條件得到同一個 8πM（`unitConeAngle_of_surfaceGravity`，兩條獨立的路），視界兩側模態的係數比 e^{−2πω/κ} 給出熱分佈（`bogoliubov_ratio_sq_tendsto`、`bogoliubov_thermal`） | `ptrB_tfdState`：TFD 的 A 側約化態是 Gibbs 態；`tfdAmp_eq_exp`：振幅就是歐氏演化 e^{−(β/2)H}；`isKMS_unique`：β 被 KMS 條件唯一刻畫；`gibbs_dS_eq_beta_dE`：dS/dβ = β·dE/dβ，所以只要 Var(H) ≠ 0，β 就是熵對能量的斜率（`gibbs_entropy_energy_slope`）——ER 側 `first_law_area` 把同一個關係（dS/dM = β）當**假設**，EPR 側它是**定理** | **單向特化**：幾何側剛性、量子側自由（§6）。斜率關係兩側同形，但值對不上（§5 不可能定理） |
| 熵 | `first_law_area`：第一定律 + 單位錐角 ⇒ S = 4πM² = A/4。假設能同時成立 `first_law_witness` | `vnEntropy_ptrA_tfdState`：TFD 兩側糾纏熵 = Gibbs 熵（由純態 S(A) = S(B) `vnEntropy_ptrA_pureOf_eq`） | **h：唯一的洞**。而且有形狀（§5） |
| 面積 vs 糾纏上界 | `throat_area_le`：喉部是面積 16πM² 的極小球面；在整個時空裡是鞍點 `area_slice_gt`／`area_timelike_lt` | `rank_cutMat_tnAmp_le`：任意圖、任意割，秩 ≤ D^{割邊數}；熵版（面積律）`cutEntropy_tnAmp_le`：任意圖、任意割，糾纏熵 ≤ 割邊數 × log D（一維特例 `vnEntropy_cut_mpsOpen_le`），等號對每個割邊數都達得到 `area_law_saturated`；緊 `rank_cutAt_bell`、`rank_cutAt_ringBell`、`vnEntropy_cut_bellN` | **只有 ≤ 半邊**。RT 的等號未證，上界對非全像網路也成立 |
| 幾何對態的約束 | 最小割函數滿足 MMI `minCut_mmi`（與次模性 `cutEdges_card_submodular`） | 四方 GHZ 的量子熵違反 MMI `ghz4_mmi_fails`，所以沒有任何圖的最小割能重現它 `ghz4_not_minCut` | **圖可實現的熵 ⊊ 量子熵**：這是中間一欄唯一有內容的離散陳述，不是 RT |

---

## 5. 洞的形狀：不可能定理

h 不能證，但可以證它**不能是什麼**：

- 任何有限維 Hermitian H，Gibbs 熵對 β **不增**：`hasDerivAt_gibbsEntropyFn`（dS/dβ = −β·Var(H)）、`energyVar_nonneg`、`antitoneOn_gibbsEntropyFn`。
- 黑洞熵 S = β²/16π 對 β **嚴格遞增**（比熱為負）。
- 所以不存在任何單一有限維 H，能在任何正長度的 β 區間上對上黑洞：`no_finite_dim_gibbs_matches_bh`；質量參數版 `no_finite_dim_gibbs_matches_bh_mass`；真的用到 ER 側錨點的耦合版 `no_gibbs_matches_first_law`（在 `Chain.lean`）。
- 單一 β 點上永遠調得到相等，所以單點相等沒有內容：`negctrl_single_point`（中間值定理）。
- 反過來，讓 H 隨 β 變，同一個維度就夠讓整段 β 都恰好對上：`negctrl_nogo_varying_hamiltonian`。兩條並排是 `nogo_hinges_on_fixed_hamiltonian`：「存在一個 H 對所有 β」為假，「每個 β 各有一個 H」為真。不可能定理排除的就是「H 固定」這一件事；洞剩下的出口是 Hilbert 空間隨質量變、微正則、或無限維。
- 健全性：β = 0 時熵 = log d `vnEntropy_gibbs_zero`，與既有的 `vnEntropy_le_log_rank` 交叉一致。
- 反過來，固定 H 時 Gibbs 態在自己那一側是「最好的」：任何態都滿足 S(σ) ≤ β·tr(σH) + log Z，等號只在 Gibbs 態（`vnEntropy_le_beta_energy_add_log`、`vnEntropy_eq_beta_energy_add_log_iff`）；能量相同時 Gibbs 態是熵唯一的最大者（`vnEntropy_lt_gibbs_of_energy_eq`）。所以不可能定理排除的不是「Gibbs 態不夠好」，而是「固定有限維 H」這個設定。這個不等式也是 Landauer 與 Bekenstein 兩種界共同的數學核心，見 `docs/TRIANGLE.md`；完整的 Landauer（抹掉一個位元至少放 T ln 2 的熱）本庫已證（`landauer`），Bekenstein 那一邊只到 ΔS ≤ Δ⟨K⟩。Landauer 要求系統與熱庫一開始沒有相關；起點換成 Bell 態，抹除就可以不放熱（`negctrl_landauer_correlated`）。這是 EPR 側的糾纏直接改寫熱力學帳本的一個小例子，同一個例子也給出條件熵為負（`bell_conditional_entropy`）。把同一個 Bell 態倒過來讀，就是「觀測」的最小模型（`ErEpr/Measurement.lean`）：CNOT 把系統的疊加態和儀器糾纏起來，只看系統時干涉項歸零、熵從 0 升到 ln 2，像是線脫落了；整體仍是純態，線其實是接到儀器上。只動系統或只動儀器都解不開，要兩端一起。最後一塊是一夫一妻（`monogamy`）：A 與 B 的聯合態一旦是純態（例如 Bell），A 與任何第三方 C 的互資訊就是 0。糾纏不能隨便共享；黑洞的防火牆悖論就卡在這一條，ER=EPR 是為了解那個矛盾提出的（本庫只有這條定理，沒有黑洞內部或輻射的模型）。糾纏交換（`entanglement_swapping`）把這幾塊接起來：兩端從沒碰過面，但中間的 B、C 做一次糾纏的測量（「相交點」），A 與 D 就接成 Bell 態，A 和 B 原本的那條線同時被放掉；四個結果平均起來 A–D 什麼都沒變（`swap_average_no_signalling`），所以接上糾纏不等於傳了訊息。

這條定理不反駁 ER=EPR。它排除一整類可能的 h：「黑洞 = 固定有限維正則系綜」一開始就不行，剩下只能走微正則或無限維。這就是「洞變小而且位置更明確」的實例。限定：只對漸近平坦黑洞；AdS 大黑洞比熱為正，不適用。

兩個獨立角色（空洞獵人、科學哲學）沒看過彼此的報告，各自推出這一條；主線另外驗算。

---

## 6. 共享 reduct：同一理論的兩個模型，不是同一個物件

兩側都滿足一小組公理：一個態 ω、一個虛時間的一步 ν、非退化性、KMS 條件。這組公理寫成 `KMSPair`。

- 結構層級的定理 `tracial_iff_period`（三行）：ω 是跡態 ⇔ ν 是恆等。
- 幾何側的代數是交換的，所以 ν 必為恆等，β 被釘死：`ofComm`。
- 量子側 ν 是恆等 ⇔ e^{−βH} 是純量 ⇔ H 是純量，否則 β 自由：`gibbs_tracial_iff_scalar`（實例 `gibbsKMSPair`）。
- 所以「溫度相等」不是對稱的等號，是**單向特化**：幾何決定溫度，量子接受它。
- 而且兩側**不同構**：矩陣代數到交換環沒有保單位的環同態 `no_ringHom_matrix_to_comm`。

結論：中間那一欄的最高身分是「共享 (β, ν, ω) 這個 reduct」，到不了同構。字典不是雙向翻譯，是一邊在約束另一邊。

關於群論：一開始提的 ℝ ⋊ Z₂ 骨架是空的，任何有不動點的集合都是模型；要有內容必須加上態與非退化性。對稱性相同只說明形狀相同，不說明是同一個東西。

---

## 7. 不能說的話

- 不說「證明／形式化／驗證了 ER=EPR」。
- 不說「機器檢查的物理」；標準三公理只擔保數學。
- 不說「只剩一個假設」而不講那個假設有多強——它可能就是整個猜想。
- 不說「首次」「首創」；上游已有量子資訊的 Lean 庫。
- 不說 TFD「最大糾纏」；它的約化態是熱態，不是單位陣。
- 不說 RT；本庫只有 ≤ 半邊。

能說的是一句條件句：**在顯式座標與有限維矩陣這兩個數學模型內，若識別假設 h 成立，則其餘等式成立；h 本身不是定理，而且它不能是某幾種東西。**

---

## 8. 讀程式碼的順序

1. `README.md` 的字典表（本導讀 §4 的來源）。
2. `NoSignalling.lean`：`ptrB_idKron`，三行；然後往上看 `Basic.lean` 的八條保真引理，那才是可信度的來源。
3. `TFD.lean`：`tfdAmp_mul_conjTranspose`（橋接引理，兩邊獨立定義才有內容）、`ptrA_tfdState`（轉置）、`tfdAmp_eq_exp`。
4. `ER.lean`、`Hawking.lean`：座標層級的 ER 側，注意每條 docstring 的範圍聲明。
5. `NoGo.lean`：不可能定理，先看 `no_finite_dim_gibbs_matches_bh` 的 docstring 再看證明。
6. `KMS.lean`、`KMSPair.lean`：`isKMS_unique`、`tracial_iff_period`。
7. `EVIDENCE.md`：當附錄查，每一節末尾的「限定」是最該用自己的眼睛判斷的部分。
