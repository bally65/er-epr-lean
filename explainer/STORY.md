# 我們這一路在做什麼（解說動畫的故事稿）

## 一句話

ER=EPR 是一個**猜想**：「蟲洞（幾何）」和「糾纏（量子）」是同一件事。它不是數學定理，所以不能直接證明。我們做的是另一件事：**把兩側能寫成數學的零件，一塊一塊證成定理，用它們把那個洞逼到角落，量出洞的形狀。**

## 分鏡

| 段 | 時間 | 畫面 | 字幕 |
|---|---|---|---|
| 1 問題 | 0–14 s | 左邊兩個黑洞用管子接起來（蟲洞）、右邊兩個點用一條亮線接起來（糾纏），中間一個「＝？」 | ER=EPR 是猜想，不是定理 |
| 2 策略 | 14–30 s | 中間一個圈（洞），兩側的定理小牌一塊塊靠過去 | 不去填洞，把洞逼到角落 |
| 3 洞的形狀① | 30–50 s | 熵對溫度的兩條曲線：固定系統的熵往下、黑洞的熵往上，只交在一點；接著換成量詞對照 | 固定的有限維系統做不到；讓 H 隨溫度變就做得到 |
| 4 洞的形狀② | 50–66 s | 三個點 A（內部）、B（晚期輻射）、R（早期輻射）；A–B 的線一亮，B–R 的線就斷 | 一夫一妻：B 不能同時和 A、R 最大糾纏（AMPS 矛盾） |
| 5 線是轉手，不是剪斷 | 66–90 s | 觀測：系統和儀器接上線，只看系統像斷了；交換：A–B、C–D 兩條線，中間一測，變成 A–D | 觀測時線轉給儀器；交換能接上糾纏，但不能傳訊息 |
| 6 怎麼確定是真的 | 90–105 s | 四個數字：定理、反向演習、耦合斷言、sorry | 洞還在，但形狀更清楚了 |

## 每段背後的定理（給對照用）

1. 兩側字典：`ER.lean`（Kruskal 不可穿越）、`Hawking.lean`（β = 8πM）、`NoSignalling.lean`、`Entropy.lean`。
2. 零件：`Landauer`、`Monogamy`、`Swapping`、`FirstLawGeneral`、`Unruh` 等 26 個模組。
3. `no_finite_dim_gibbs_matches_bh`、`negctrl_single_point`、`nogo_hinges_on_fixed_hamiltonian`。
4. `monogamy`、`amps_contradiction`、`amps_each_half_satisfiable`、`negctrl_amps_mixed`。
5. `measurement_dephases`、`local_cannot_undo`、`pointer_cannot_undo`、`entanglement_swapping`、`swap_average_no_signalling`。
6. 599 條定理（只用標準公理）、95 份反向演習、91 條耦合斷言、0 個 `sorry`（2026-10-25 補面積律後的數字）。

## 不能說的

- 這支動畫不說「證明了 ER=EPR」或「否定了 ER=EPR」。
- 圖都是示意：曲線的形狀對，數值不按比例；蟲洞只是一個符號。
