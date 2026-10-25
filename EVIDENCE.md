# 編譯證據

> **公開版說明**：這個 repo 的 `evidence/` 只保留兩種檔案：每次乾淨重建（`*_lakebuild/`）的收據 `receipt.txt`、公理清單 `axioms.out`、耦合結果 `coupling.out`，以及每次全量重跑演習的報告 `drills_*/REPORT.md`。下文提到的其他證據目錄（探針、逐份演習的編譯紀錄）只留在作者的私人 repo。

## 第一批：Basic＋T1（2026-10-23）

- 節點：lean-node（Hyper-V VM）。
- 版本：Lean 4.33.1，mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。借 `~/alloy_node/src/chemical_quantum` 現成的 mathlib，節點上沒有安裝任何東西。
- 編譯指令：每個模組各跑一次 `nice -n 19 prlimit --core=0:0 lean -M 8192 -j 1 -DwarningAsError=true -o … -i …`，順序是 Basic → NoSignalling → Axioms。
- olean 只寫進該次證據目錄的 `build/`。
- 腳本：`tools/node_run.sh`（Mac → 節點單行道，跑完收回）、`tools/run_probe.sh`（在節點上執行）。

### 正式結果

證據目錄：`evidence/er_epr_20261023T104139Z_iter4/`

- 結果：rc=0，三個模組都沒有錯誤，也沒有警告。
- 公理：27 條定理全部只依賴 `[propext, Classical.choice, Quot.sound]`，見 `lean_Axioms.out`。
- 檔案 sha256（與 repo 現行檔一致）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Basic.lean` | 5c5ff1c3235704f7663dba551641fa6c789a1f8b4fd672079e741292ab1c5be7 |
| `ErEpr/NoSignalling.lean` | 7895c0bc5af436af4e6f5a30cad2f2785d6cd134fd914baaccdfc6bfd55af826 |
| `ErEpr/Axioms.lean` | 16399b0a91ed71157391308fa05fd7df2a00232aafa4467569532780ee0449dd |

- 資源：峰值 RSS 約 6.59 GB；三個模組各約 2–4 秒（mathlib 已預熱）。

### 修正過程

`first`、`iter2`、`iter3` 三次都是 rc=1，錯誤內容如下，沒有涉及數學內容：
- `smul_apply` 名稱有歧義。
- 多列了沒用到的 simp 參數。因為開了 warningAsError，這類 linter 警告也算錯誤。
- 目標已經被 simp 關掉，後面的 `norm_num` 變成多餘。
- 複數共軛作用在數字上，simp 需要補 `map_ofNat` 才能化簡。

### 反向演習

做法：先把定義或假設故意改壞，確認改動真的寫進檔案（`diff`），再送節點編譯。改壞的副本放在 session 的 scratchpad，跟 repo 分開。

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R1 `…_drill_R1` | `ptrB` 改成 `∑ k, X (j,k) (i,k)`（列行指標對調） | rc=1 | F1 `trace_ptrB_mul`、F2 `ptrB_kronecker`、`ptrA_apply` 等 |
| R2 `…_drill_R2` | `idKron` 取錯區塊：`blk X p.1 p.1` | rc=1 | F7 `idKron_kronecker`、`ptrB_idKron_apply` |
| R3 `…_drill_R3` | 刪掉 T1 的保跡假設 `hTP` | rc=1 | T1 `ptrB_idKron` 的證明，以及所有下游呼叫 |
| R3b `…_drill_R3b` | `Kraus.tp` 改成 unital：`Σ K Kᴴ = 1` | rc=1 | `Kraus.trace_toLin` |

**限定**：反向演習只證明「改壞之後證明跑不過」，並沒有另外證明「改壞後的陳述是假的」。
「是假的」這一半，已經由負控制正面證過：
- N1：拿掉保跡，結論為假。
- N2：unital 不等於保跡。
- N3：結論不是「所有邊際都不變」。
- N4：局域性是必要的。

## T2 熱場雙態（2026-10-23）

版本與指令同第一批。模組順序改為 Basic → NoSignalling → TFD → Axioms。

### 正式結果

證據目錄：`evidence/er_epr_20261023T105728Z_t2_iter3/`

- 結果：rc=0，四個模組都沒有錯誤，也沒有警告。
- 公理：41 條定理全部只依賴 `[propext, Classical.choice, Quot.sound]`，含 T2 的 14 條。
- 檔案 sha256（與 repo 現行檔一致）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Basic.lean` | 5c5ff1c3235704f7663dba551641fa6c789a1f8b4fd672079e741292ab1c5be7 |
| `ErEpr/NoSignalling.lean` | 7895c0bc5af436af4e6f5a30cad2f2785d6cd134fd914baaccdfc6bfd55af826 |
| `ErEpr/TFD.lean` | 6b59b9607a2ff9730b9889b5270e16169e1fb8210558c707b02e69be2f9418f8 |
| `ErEpr/Axioms.lean` | df298f0ae70b1d8d909677728b35aa82b5dab15f3149fce946342da29ff8cb15 |

- 資源：TFD 模組約 5 秒，峰值 RSS 約 6.6 GB。

### 修正過程

橋接引理第 3 輪就過了，沒有觸發停損（上限 6 輪）。

- `t2_iter1`：錯誤有五類。
  - `coe_star` 多寫了。
  - simp 太早把實指數轉成複指數。
  - σ_y 的矩陣乘法被 simp 展成向量乘法後停住。
  - linarith 收到的假設形狀不對。
  - 有一個沒用到的 simp 參數。
- `t2_iter2`：只剩數值見證。simp 把實數轉型推進了複對數。
- `t2_iter3`：全部通過。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R4 `…_drill_R4` | 振幅右側用 `Uᵀ`，不用 `Uᴴ`（u⊗u，少了共軛） | rc=1 | `tfdAmp_conjTranspose`、橋接 `tfdAmp_mul_conjTranspose` |
| R5 `…_drill_R5` | `gibbs` 的 β 改成正號 | rc=1 | 教科書 Boltzmann 驗證 `gibbs_diagonal_real`、T2a、T2b、σ_y 見證 |
| R6 `…_drill_R6` | 振幅漏掉 1/2 | rc=1 | `tfdAmp_conjTranspose`、橋接引理 |

**R4 的限定**：設計稿預測 R4 會「T2a 照過、T2b 紅燈」。實際上 T2a 和 T2b 一起斷了，因為兩者的證明都經過「振幅是 Hermitian」這一步。所以「T2a 與 T2b 能分辨 u⊗ū 和 u⊗u」這件事，演習沒有直接驗到。
- 已經有的保護：T2b 的陳述本身，加上 σ_y 的 T2c／N5，正面證明了 B 側是轉置、不是 Gibbs 態。
- R4、R6 紅在 `tfdAmp_conjTranspose`，有一部分原因是該證明裡的輔助式寫死了振幅形式。真正有意義的紅燈在橋接引理。

## T3 MPS 秩上界（2026-10-23）

版本與指令同前。模組順序：Basic → NoSignalling → TFD → MPS → Axioms。

### 正式結果

證據目錄：`evidence/er_epr_20261023T110437Z_t3_iter2/`

- 結果：rc=0，五個模組都沒有錯誤，也沒有警告。
- 公理：48 條定理全部只依賴 `[propext, Classical.choice, Quot.sound]`，含 T3 的 7 條。
- 檔案 sha256（與 repo 現行檔一致）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Basic.lean` | 5c5ff1c3235704f7663dba551641fa6c789a1f8b4fd672079e741292ab1c5be7 |
| `ErEpr/NoSignalling.lean` | 7895c0bc5af436af4e6f5a30cad2f2785d6cd134fd914baaccdfc6bfd55af826 |
| `ErEpr/TFD.lean` | 6b59b9607a2ff9730b9889b5270e16169e1fb8210558c707b02e69be2f9418f8 |
| `ErEpr/MPS.lean` | b165e1259dacfb4da9d9d0f56c02ccd24cae813c5122a58193186f220033dd5f |
| `ErEpr/Axioms.lean` | bcdd92949156d6d43cbf72ee7b7b41de474082c7effa9151bbaf6fdd206e980f |

- 資源：MPS 模組約 3 秒，峰值 RSS 約 6.6 GB。

### 修正過程

- `t3_iter1`：只有 Bell 振幅那條沒過。simp 化簡後還需要對 x₀、x₁ 分情況。
- `t3_iter2`：全部通過。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R7 `…_drill_R7` | 開邊界上界收緊成 `D - 1` | rc=1 | T3a `rank_cutAt_mpsOpen_le`、推論 `rank_ptrB_mpsOpen_le` |
| R8 `…_drill_R8` | 環狀上界收緊成 `D`（假裝只割 1 條鍵） | rc=1 | T3b `rank_cutAt_mpsRing_le` |
| R9 `…_drill_R9` | 鏈乘積順序反過來（`.reverse.prod`） | rc=1 | 切分引理 `chainProd_append`、Bell 振幅 |

**限定**：
- R7 收緊之後的說法確實是假的。Bell 緊度見證 `rank_cutAt_bell` 已證明秩恰好是 2 = D，所以 D − 1 不成立。
- R8 只證明證明跑不過，沒有證明「環狀 ≤ D」是假的。本庫沒有環狀秩超過 D 的見證，D² 的上界是否緊，也沒有見證。

## 第二批：von Neumann 熵（2026-10-23）

版本與指令同前。模組順序：Basic → NoSignalling → TFD → MPS → Entropy → Axioms。

### 正式結果

證據目錄：`evidence/er_epr_20261023T111720Z_s2_iter4/`

- 結果：rc=0，六個模組都沒有錯誤，也沒有警告。
- 公理：62 條定理全部只依賴 `[propext, Classical.choice, Quot.sound]`，含第二批的 14 條。
- 檔案 sha256（與 repo 現行檔一致）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Basic.lean` | 5c5ff1c3235704f7663dba551641fa6c789a1f8b4fd672079e741292ab1c5be7 |
| `ErEpr/NoSignalling.lean` | 7895c0bc5af436af4e6f5a30cad2f2785d6cd134fd914baaccdfc6bfd55af826 |
| `ErEpr/TFD.lean` | 6b59b9607a2ff9730b9889b5270e16169e1fb8210558c707b02e69be2f9418f8 |
| `ErEpr/MPS.lean` | b165e1259dacfb4da9d9d0f56c02ccd24cae813c5122a58193186f220033dd5f |
| `ErEpr/Entropy.lean` | afb9964a10fc78945ed9a4f93766c75cd7331543d42264a68c549acdf8c6a571 |
| `ErEpr/Axioms.lean` | 811ea0801b642f6bb3633f8233af8ad7d68be99ee5551cd1cd3c6694dea2278d |

- 資源：Entropy 模組約 3 秒，峰值 RSS 約 6.6 GB。

### 修正過程

- `s2_iter1`：錯誤都是寫法問題，沒有數學錯誤。
  - `congr 1` 已經把目標關掉，後面幾行多餘。
  - 最大混合態的係數被解讀成實數純量乘法。
  - lambda 少了型別標註。
  - 有一個沒用到的 simp 參數。
- `s2_iter2`：全部通過。
- `s2_iter3`、`s2_iter4`：補上負控制 N8；iter3 只因一個沒用到的 simp 參數失敗。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R10 `…_drill_R10` | 拿掉 S ≤ log rank 的「跡為 1」 | rc=1 | `vnEntropy_le_log_rank`、`vnEntropy_le_log_of_rank_le` |
| R11 `…_drill_R11` | 熵定義改取虛部 `z.im` | rc=1 | `vnEntropy_eq_sum_eigenvalues`、Shannon 健全性 `vnEntropy_diagonal`、`vnEntropy_mul_comm` |
| R12 `…_drill_R12` | 環狀熵上界收緊成 `log D` | rc=1 | `vnEntropy_cut_mpsRing_le` |

**限定**：
- **R10**：拿掉「跡為 1」之後，S ≤ log rank 確實是錯的。這由 N8 `negctrl_unnormalized` 正面證明：diag(1/e, 1/e) 的熵 2/e 大於 log 2。
- **R11**：`vnEntropy_mul_comm` 紅燈，主要是因為它和輔助引理的寫法對不上，不能算語意上的紅燈。語意上的紅燈是兩條健全性見證。
- **R12**：只證明證明跑不過。本庫沒有環狀熵超過 log D 的見證，2 log D 是否緊也沒有見證。

## 根檔與 lakefile（2026-10-23）

- 證據目錄：`evidence/er_epr_20261023T120310Z_root_check/`。
- 根檔 `ErEpr.lean` 只 import 五個模組，在節點上編過（`rc_root=0`）。
- 全套模組重編一次，62 條公理檢查仍全綠。
- `lakefile.toml` 與 `lake-manifest.json` 是新加的，`lake build` 的驗證見下一節。

## lake build 乾淨驗證（2026-10-23）

證據目錄：`evidence/er_epr_20261023T120834Z_lakebuild/`。腳本：`tools/lake_build_node.sh`。

### 做法

- **工作目錄**：在節點的全新目錄 `~/alloy_node/lakebuild/` 下，解開 `git archive HEAD` 的內容（commit `372f612`，不含 `evidence/`）。
- **抓依賴**：`lake exe cache get`。lake 依 manifest 從 GitHub 抓了 mathlib 與 8 個傳遞依賴，用時 1 分 48 秒。olean 從節點本機的 mathlib 快取區解壓了 8,689 個（log 寫 `already-cached`），這批快取原本就是從官方伺服器下載的，這次沒有重新下載。
- **建置**：逐模組依序跑 `lake build --wfail <模組>`，每次只有一個 lean。這是為了不和節點上另一個 SDP 探針工作搶記憶體；那個工作不是本 session 開的，沒有動它。之後再跑一次不指定目標的 `lake build --wfail`。
- **公理檢查**：`lake env lean -M 8192 -j 1 -DwarningAsError=true ErEpr/Axioms.lean`。
- **限制**：lake 沒辦法把 `-M 8192` 傳給它啟動的 lean。上面逐步建置時，每一步前都確認可用記憶體 ≥ 20 GiB；實測峰值 RSS 是 6.8 GB。

### 結果

- **建置**：`rc_cache_get=0`。六個逐步建置都是 rc=0：Basic、NoSignalling、TFD、MPS、Entropy、根檔 `ErEpr`，每個 3–5 秒，都由 lake 實際編譯。最後的完整 `lake build` 也是 rc=0（8,712 jobs），沒有需要重編的東西。
- **公理**：`rc_axioms=0`，62 條全部只依賴標準三公理。
- **manifest**：sha256 在抓依賴前、抓依賴後、建置後三次都相同，lake 沒有改寫它。
- **套件版本**：9 個套件的 git HEAD 與 manifest 的 rev 逐一相符（`package_heads.txt`）。
- **原始碼**：各檔 sha256 與 repo 現行檔一致（`receipt.txt`）。
- **磁碟**：`.lake` 佔 7.6 GB。

### 第一次嘗試（未執行）

`er_epr_20261023T120706Z` 被守門擋下，記憶體不足沒有跑，沒有留下證據目錄。當時節點上另一個工作佔用了記憶體，可用記憶體只剩 22.5 GiB，低於當時設的 30 GiB 門檻。之後改成逐模組建置，門檻降到 20 GiB，才跑出上面的結果。

## ER 側：ER-1、ER-2（2026-10-23）

證據目錄：`evidence/er_epr_20261023T133204Z_er_iter3/`。版本與逐檔指令同前，模組順序加入 `ER`。根檔 `ErEpr.lean` 也 import 了 `ErEpr.ER`。

### 正式結果

- 結果：rc=0，所有模組與根檔都沒有錯誤，也沒有警告。
- 公理：73 條定理全部只依賴標準三公理，其中 ER 側 11 條。
- 新檔 sha256（舊檔不變，與前一節一致）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/ER.lean` | cfcee698a509080b44ff6bea06f045015d6587471b6febdcbc79bccd1fd3067d |
| `ErEpr/Axioms.lean` | 0f9be3fbd939c18aa13932e35c044becbe78648d9c4658c074ee0bc695543d92 |
| `ErEpr.lean` | 269809b4579bdc63d1fd40de13bbff0310443a191bf29acf7218f179e21837a3 |

### 修正過程

- `er_iter1`：錯誤有三類。
  - `push_neg` 在這版 mathlib 已棄用。
  - 一處多餘的 `ring`。
  - 反演導數用 `convert` 時拆出型別類目標，改成先改寫函數再用 `congr_deriv`。
- `er_iter2`：全部通過。
- `er_iter3`：補強負控制，改用一條指向未來但類空的曲線。原本 t = 0 切片上的曲線保留下來，當作見證。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R13 `…_drill_R13` | `FutureCausal` 拿掉因果不等式 `-F U' V' + A ≤ 0` | rc=1 | `FutureCausal.nonneg` |
| R14 `…_drill_R14` | 喉部面積下界收緊成 `17πM²` | rc=1 | `throat_area_le` |
| R15 `…_drill_R15` | 反演改成 `M²/2ρ` | rc=1 | `inversion_isometry` |

**限定**：
- **R13**：拿掉因果不等式之後，結論確實是假的。`negctrl_spacelike_connects` 的曲線切向量是 (3, −2)，指向未來但類空，滿足被削弱的條件，而且連通了兩個外區。
- **R14**：收緊之後的下界確實是假的。`throat_area_eq` 證明最小值恰好是 16πM²。
- **R15**：只證明證明跑不過，沒有另外證明改壞後的陳述是假的。
- 這次沒有重跑 `lake build`。逐檔編譯含根檔都通過，但 lake 的乾淨驗證停留在 commit `372f612` 的內容。

## ER-3 與收尾（2026-10-23）

證據目錄：`evidence/er_epr_20261023T134558Z_hk_iter3/`。模組順序加入 `Hawking`，根檔也 import 了它。

### 正式結果

- 結果：rc=0，所有模組與根檔都沒有錯誤，也沒有警告。
- 公理：80 條定理全部只依賴標準三公理，其中 ER-3 與收尾 7 條。
- 新檔 sha256：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Hawking.lean` | bf160a4d8a8ad2da2e635864f7c2d512c332c587b40d52cacc042544540633fa |
| `ErEpr/Axioms.lean` | 477ba9b990a95e6f769ab5a53f315febca01052aa5355b65fda2266aaf0db707 |
| `ErEpr.lean` | 139502306475705c0120b0e00217743ae1c563bb6c9177075c36984360a95896 |

### 修正過程

3 輪就過了，沒有觸發停損。

- `hk_iter1`：錯誤有兩類。
  - `convert` 又拆出型別類目標，改用 `congr_deriv`。
  - 連續函數的常數項推不出來，改成先寫出連續性。
- `hk_iter2`：還剩三處。
  - 有一處 `x⁻¹⁻¹` 讓 `ring` 卡住，先用 `div_div_eq_mul_div` 改寫。
  - 另外兩處 `convert` 改用 `congr_deriv`。
- `hk_iter3`：全部通過。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R16 `…_drill_R16` | 固有距離的被積函數漏掉係數 2 | rc=1 | `properDist_hasDerivAt` |
| R17 `…_drill_R17` | `hawking_beta` 改宣稱 β = 4πM | rc=1 | `hawking_beta`，以及用到它的 `first_law_area`、`first_law_witness` |
| R18 `…_drill_R18` | 收尾改宣稱 S = 8πM² | rc=1 | `first_law_area` |

**限定**：
- **R17**：改壞的說法確實是假的。`negctrl_wrong_beta` 證明 β = 4πM 時極限是 1/2，不是 1。
- **R18**：改壞的說法確實是假的。`first_law_witness` 證明 S = 4πm² 滿足所有假設，而 4πM² ≠ 8πM²。
- **R16**：紅在導數引理，那是陳述與定義直接不符。下游定理的證明會改用被 sorry 補上的版本，所以沒有一起列出紅燈。

## 最終版 lake build 乾淨驗證（2026-10-23）

證據目錄：`evidence/er_epr_20261023T135138Z_lakebuild/`。驗證對象是 commit `930400b`，含 ER、Hawking 與兩欄字典表。

- **做法**：同上一次。全新目錄，解開 `git archive HEAD`，依 manifest 抓依賴，跑 `lake exe cache get`，再逐模組 `lake build --wfail`（含 `ErEpr.ER`、`ErEpr.Hawking`），最後整包跑一次 `lake build --wfail`。
- **節點狀況**：另一個 session 的 SDP 探針工作仍在跑，每一步建置前可用記憶體約 31 GiB，都高於 20 GiB 門檻。
- **建置**：8 個逐步建置與最後的完整 `lake build` 都是 rc=0（8,714 jobs）。
- **公理**：`rc_axioms=0`，80 條全部只依賴標準三公理。
- **manifest**：sha256 三次都相同，lake 沒有改寫它；9 個套件的 HEAD 與 manifest 逐一相符。
- **原始碼**：節點上的原始碼 sha256 與 repo 現行檔逐一相符。

## 補缺口（2026-10-23）

證據目錄：`evidence/er_epr_20261023T142325Z_gap_iter4/`。

### 正式結果

- 結果：rc=0，所有模組與根檔都沒有錯誤，也沒有警告。
- 公理：87 條定理全部只依賴標準三公理，其中新增 7 條。
- 檔案 sha256（其餘檔不變）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/TFD.lean` | c98cef11ea090ad3ef87d1eeac6d80d0d6f95eb629a891805b2eeab46f02d92f |
| `ErEpr/MPS.lean` | 16344a21a8c0fa90694df5493a6bbe64814df26b0b27c1440d216dc780a47092 |
| `ErEpr/NoSignalling.lean` | f61e0251b33e2e7bb93ead885b83c9354ea9a68d08172c8f9af495407265603c |
| `ErEpr/Axioms.lean` | ce281441b13778d5d80d18540a492d7607eb1e958ef6dc66b2fa3083da652725 |
| `ErEpr.lean` | 139502306475705c0120b0e00217743ae1c563bb6c9177075c36984360a95896 |

### 補了什麼

- **T2d `tfd_boost_invariant`**：(H⊗1 − 1⊗Hᵀ)\|TFD⟩ = 0。另外補了輔助引理 `kron_mulVec_vecOf`、`commute_tfdAmp`。
- **u⊗ū `vecOf_tfdAmp`**：原本這只寫在 TFD 的註解裡，現在是定理。
- **錯振幅負控制 `negctrl_wrong_amplitude`**：取代 R4 演習。錯誤振幅 U·D·Uᵀ 照樣通過 T2a（`ptrB_pureOf_wrong`），但它的 B 側約化態是 Gibbs 態本身（`ptrA_pureOf_wrong`），在 σ_y 下就違反 T2b。T2c、R4 那一節的限定（「T2a 與 T2b 能分辨 u⊗ū 和 u⊗u 沒有直接驗到」）到此解除。
- **環狀緊度 `rank_cutAt_ringBell`**：兩組 Bell 對各跨一條鍵，秩恰為 4 = D²。T3 那一節「D² 是否緊沒有見證」到此解除。
- **轉置不是完全正 `transposeMap_not_completelyPositive`**：Bell 態半正定，但 id⊗T 之後在 \|01⟩ − \|10⟩ 上的期望值是 −1。

### 修正過程

- `gap_iter1`：沒有執行。守門腳本把 `/usr/bin/time` 包裝也算成 lean 程序，誤判為 12 個。當時節點上實際是另一個 session 的 `lb_scale_probe` 在跑，有 6 個 lean。守門改用 `pgrep -xc lean` 之後才正確。
- `gap_iter2`：只有 `vecOf_tfdAmp` 沒過，simp 先展開了內層乘法。
- `gap_iter3`：TFD 部分全過。
- `gap_iter4`：加入環狀見證與「轉置不是完全正」，一次就過。

### 反向演習

| 演習 | 改動 | 結果 | 紅在哪裡 |
|---|---|---|---|
| R19 `…_drill_R19` | 反對稱向量改成對稱的 \|01⟩ + \|10⟩ | rc=1 | `transposeMap_not_completelyPositive` |
| R20 `…_drill_R20` | T2d 的 Hᵀ 改成 H | rc=1 | `tfd_boost_invariant` |

**限定**：R19、R20 只證明證明跑不過，沒有另外證明改壞後的陳述是假的。

## 補缺口後的 lake build 乾淨驗證（2026-10-23）

證據目錄：`evidence/er_epr_20261023T142705Z_lakebuild/`。驗證對象：commit `fd7d916`。

- 第一次嘗試被守門擋下，沒有留下證據目錄：當時另一個 session 的 `lb_scale_probe` 正有 6 個 lean 在跑，而 lake build 腳本的門檻是 5。
- 改成先等節點空下來（真正的 lean 程序少於 2 個）再開跑。實際等待 0 秒。
- 結果：`rc_cache_get=0`；8 個逐步 `lake build --wfail` 與最後的完整 `lake build --wfail` 都是 rc=0。
- 公理：`rc_axioms=0`，87 條全部只依賴標準三公理。
- manifest 三次 sha256 相同；套件 HEAD 與 manifest 相符；原始碼 sha256 與 repo 相符。

## Opus 5.5 代工批次：環狀熵緊度、衛生、一般圖「∀割」（2026-10-23）

實作：Opus 5.5 子代理。驗收：主線親自對照證據目錄、公理、演習與定理陳述（見本節末）。

### 正式結果

證據目錄：`evidence/er_epr_20261023T151054Z_C_iter3/`（最終版，含全部模組與根檔）。

- 結果：rc=0，所有模組與根檔都沒有錯誤，也沒有警告。
- 公理：107 條定理全部只依賴標準三公理（A 之後 91、C 之後 107）。
- 全庫已無任何 `set_option`。
- 檔案 sha256（與 repo 現行檔逐一相符）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Basic.lean` | 6ba9e26957abb2623bb823500da90821af3c55f25fc57416b184bb0bde2416a9 |
| `ErEpr/NoSignalling.lean` | f3f4258afc6dbd27ee31c0915d312429038804f2a809fbc60399975500b315b5 |
| `ErEpr/TFD.lean` | 4708341b6cfa833b9d90d665f89d2a9cd23cbf98fcc9a692d6c80b4b30b13ab9 |
| `ErEpr/MPS.lean` | 4641fa2de5e31a8ff72711e01958b1222b58473a1af4a874e5f25ab1b9874e10 |
| `ErEpr/Entropy.lean` | 5f3c53b743286409157c14fff42b1615136dc21303ecca4d4559d2729ebfca08 |
| `ErEpr/ER.lean` | cfcee698a509080b44ff6bea06f045015d6587471b6febdcbc79bccd1fd3067d |
| `ErEpr/Hawking.lean` | bf160a4d8a8ad2da2e635864f7c2d512c332c587b40d52cacc042544540633fa |
| `ErEpr/TensorNetwork.lean` | 42510c4bdb0dabdfdfc81151118bd1538059b2cb133b4f7c65d5d2482f0305c1 |
| `ErEpr/Axioms.lean` | 79e363d515bf4bbce40759f7b5600f4144603d936510f686cc00031de0266700 |
| `ErEpr.lean` | a7357955a408b41f30b12e87d446dfbecac97ef1cd4a0deebc6265437688c4db |

- 中途證據：`…144459Z_A_iter1`（A 完成，91/91）、`…145009Z_B_iter3`（B 完成，91/91）。
- **非正式**：`…144045Z_diagB_warnings`、`…144822Z_diagB2` 是診斷用，裡面的副本插了 `warningAsError false`，不能當證據。

### 新增

- **A**：`cutAt_mpsRing_smul`（每個張量乘 c，切口乘 c^(k+m)）、`cutAt_ringBellN`（= (1/2)·1₄）、`trace_ringBellN`（= 1）、`vnEntropy_cut_ringBellN`（= 2 log 2）。先前「環狀熵上界 2 log D 是否緊沒有見證」的限定到此解除。
- **B**：各檔 `variable` 縮小、`omit … in` 共 11 處；`TFD.lean` 的 `<;> ring` 鏈改成逐行；`node_run.sh` 在子 shell 裡讀 `node.env.lean-node` 的 `NODE_HOST`／`NODE_USER`／`NODE_PORT`，B_iter1 之後每一輪都用新版腳本跑，確認可用。
- **C**（`TensorNetwork.lean`）：
  - 定義：`Inc`（入射）、`tnAmp`（振幅，頂點張量的鍵引數型別是「入射邊 → Fin D」）、`cutMat`（依頂點子集 W 重排）、`IsCut`／`cutEdges`（恰一端在 W）。
  - 主定理 `rank_cutMat_tnAmp_le`：秩 ≤ D^(割邊數)。證法：邊分三類，`∑_b` 拆三重、`∏_v` 依 W 拆，得 `cutMat_tnAmp`（左 × 右，內指標＝割邊 → Fin D）。
  - 局域性引理 `inW_of_inc_mem`、`not_inW_of_inc_nmem`。
  - 保真 `tnAmp_path2TN`（= `mpsOpen`）、`tnAmp_ring2TN`（= `mpsRing`）；見證 `rank_cutMat_bellTN`（割 1、秩 2）、`rank_cutMat_ringBellTN`（割 2、秩 4）。
  - 負控制 `negctrl_nonlocal_tensor`：`tnAmpAll`（張量看得見全部邊）配一條只接在頂點 0 的自環，割邊數 0 而秩 2。

### 反向演習（在最終版副本上做，每次只改一處）

| 演習 | 改動 | 證據目錄 | 紅在哪裡 |
|---|---|---|---|
| TN1a | 主定理的張量改成看得見全部邊 | `…151215Z_drill_TN1a` | `rank_cutMat_tnAmp_le`，三個見證連帶紅 |
| TN1b | `Inc := True` | `…151217Z_drill_TN1b` | 兩條局域性引理與兩個邊的建構子；主定理本身沒紅（它的證明只透過這些引理用到 `Inc`） |
| TN2 | 指數改成 card − 1 | `…151219Z_drill_TN2` | 主定理、兩個見證 |
| TN3 | `cutEdges` 改成數內邊 | `…151221Z_drill_TN3` | 主定理、三條 `card_cutEdges_*` 被 `decide` 證偽 |

**限定**：
- TN1a 改壞後的陳述確實為假：`negctrl_nonlocal_tensor` 正面證明。
- TN2 改壞後的陳述為假，可由 `rank_cutMat_bellTN`（2 > 2⁰）推出，但沒有寫成定理。
- TN1b、TN3 只證明證明跑不過。
- 只做了兩格點的路徑與環的保真，一般 n 格點路徑未做。
- σ 依頂點而變，D 全圖一致。
- `prod_split_mem` 用 `convert` 對齊兩個 `Fintype` 實例。

### 主線驗收紀錄

- 對照 `C_iter3` 的 receipt：全模組 rc=0；`lean_Axioms.out` 107/107 標準三公理；各檔 sha256 與工作樹相符。
- 親讀 `TensorNetwork.lean` 的定義與主定理陳述：V、E、σ v、W 都是任意的；張量的鍵引數型別確為入射邊子型別；`cutEdges` 確為「恰一端在 W」；沒有削弱。
- 親讀四份演習的 diff，確認每份只改一處；用行號對回定理名，與回報一致。
- 全庫 grep：`set_option` 0 筆；`tools/*.sh` 無位址。

## Opus 批次後的 lake build 乾淨驗證（2026-10-23）

證據目錄：`evidence/er_epr_20261023T151618Z_lakebuild/`。驗證對象：含 `TensorNetwork` 的工作樹（即提交 `Opus 5.5 batch` 的內容）。

- 全新目錄、依 manifest 抓依賴、`lake exe cache get`、9 個逐步 `lake build --wfail`（含 `ErEpr.TensorNetwork`）與最後完整 `lake build --wfail`，全部 rc=0。
- 公理：`rc_axioms=0`，107 條全部只依賴標準三公理。
- manifest 三次 sha256 相同；9 個套件 HEAD 與 manifest 相符；節點上的原始碼 sha256 與 repo 相符。
- 節點當時另一個 session 的工作已結束，等待 0 秒即開跑。

## B0 修 overclaim ＋ B1 不可能定理（2026-10-24，Opus 5.5 實作、主線驗收）

證據目錄：`evidence/er_epr_20261023T165211Z_b1_iter2/`（最終版，含全部模組與根檔）。

### 正式結果

- 結果：rc=0，12 個模組與根檔都沒有錯誤，也沒有警告。
- 公理：146 條定理全部只依賴標準三公理（原 107 條 + 新 39 條）。全庫無 `set_option`、無 `sorry`。
- 檔案 sha256（其餘檔不變）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/TFD.lean` | 8b7b65c4367ba339bb34247dce43326755a13d480cebcfb5a8e4a50ab4418bf5 |
| `ErEpr/Hawking.lean` | 3b7deb0bb7230bd958d3cf478b0a010feb79d7c903d674673ba90e2c6fa29bf2 |
| `ErEpr/NoGo.lean` | 37795e25f50307750c202abd190da31b887ec2eef8f28e8c4934c59aeded8f9c |
| `ErEpr/Chain.lean` | 22aa3f4ab1ff86f1485a598241ca3515dc80d39c0fc66eac5a34c20c35dcb250 |
| `ErEpr/Axioms.lean` | 9cc2f8c746759b66055beb3f6e312e25c9f206023ce9b2d06ce9c21972ce85c2 |
| `ErEpr.lean` | 8c8bc2c7c1030cd4cb58830baec04c0db9813f1b5cc4c9e0b35deb59449c3ed4 |

- 中途證據：`…165009Z_b0_iter1`（B0 單獨，117/117）；`…165011Z_b1_iter1` 紅在 `gibbs_zero`，補 `rfl` 後過。

### 新增

- **B0**（`Hawking.lean`、`TFD.lean`、`Chain.lean`）：`coneAngleRatio`、`UnitConeAngle`、`conicalRatio_eq_coneAngleRatio`、`coneAngleRatio_cone`（錐角 2πc 的錐比值恰為 c）、`coneAngleRatio_cone_not_unit`、`negctrl_first_law_const`、`boost_invariant_iff_commute`、`boost_invariant_one`、`tfd_boost_invariant_zero`、`ptrB_idKron_tfdState`。`hawking_beta`、`negctrl_wrong_beta`、`first_law_area`、`first_law_witness` 的陳述改用 `UnitConeAngle`，數學內容不變，docstring 改成「單位錐角條件（一階、必要），充分性未證」。
- **B1**（`NoGo.lean`）：`bw`／`partZ`／`partN`／`partQ`／`energyVar`／`gibbsEntropyFn`；`gibbs_eq_conj`、`vnEntropy_gibbs`、`vnEntropy_gibbs_eq_fn`、`hasDerivAt_gibbsEntropyFn`（dS/dβ = −β·Var，與主線手算一致）、`energyVar_nonneg`、`antitoneOn_gibbsEntropyFn`、`no_gibbs_entropy_strictMonoOn`、`no_finite_dim_gibbs_matches_bh`、`_mass`、`vnEntropy_gibbs_zero`、`vnEntropy_gibbs_le_log_card`（與 `vnEntropy_le_log_rank` 交叉一致）、`negctrl_single_point`（IVT，維度 ≥ 2）、`negctrl_single_point_H2`、`gibbs_posSemidef`、`trace_gibbs`。
- **耦合版**（`Chain.lean`）：`no_gibbs_matches_unitConeAngle`、`no_gibbs_matches_first_law`，證明體直接呼叫 `hawking_beta` 與 `first_law_area`。

### 反向演習與耦合檢驗

| 演習 | 改動 | 證據目錄 | 紅在哪裡 |
|---|---|---|---|
| NG1 | `AntitoneOn` 改 `MonotoneOn` | `…165503Z_drill_NG1` | `antitoneOn_gibbsEntropyFn`、`no_gibbs_entropy_strictMonoOn`、`vnEntropy_gibbs_le_log_card` |
| NG2 | β²/16π 改 −β²/16π | `…165506Z_drill_NG2` | B7、B8 |
| NG3 | 刪 `c ≠ 0` | `…165509Z_drill_NG3` | `negctrl_first_law_const` |
| NG4 | 真錐極限 c 改 2c | `…165555Z_drill_NG4` | `coneAngleRatio_cone`、`_not_unit` |
| 耦合 | `hawking_beta` 的 8πM 改 4πM | `…165558Z_drill_COUPLE` | `hawking_beta`、`first_law_area`、`first_law_witness`、`negctrl_first_law_const`；**NoGo 仍綠**（它本來就不依賴 ER 側） |

**限定**：
- NG2 改壞後的陳述其實仍為真（S ≥ 0 > −β²/16π），所以這份演習只顯示證明路線用到「遞增」，不是「遞減的黑洞側就不矛盾」。
- NG3、NG4 只證明證明跑不過，沒有另證改壞後的陳述為假。
- 耦合演習在 `Hawking` 紅之後腳本就停，`Chain.lean` 的兩條耦合定理沒有被單獨觀察到變紅；它們依賴 `hawking_beta` 只由原始碼可見（證明體直接呼叫），沒有用 `getUsedConstants` 機械驗。
- B0 範圍內未做：ρ + ρ² 反例、`cutSize`／`minArea` 符號拆開。

### 主線驗收紀錄

- 對照最終證據：全模組 rc=0；146/146；各檔 sha256 與工作樹相符；`set_option` 0、`sorry` 0。
- 親讀 `NoGo.lean` 的 `energyVar`、`gibbsEntropyFn`、B4 導數式、B7／B8 陳述、`negctrl_single_point` 陳述；`Chain.lean` 的 `no_gibbs_matches_first_law` 陳述與證明體（確認呼叫 `hawking_beta`、`first_law_area`）；`Hawking.lean` 的 `UnitConeAngle` 與 `hawking_beta` 新陳述。沒有削弱。

## B0＋B1 後的 lake build 乾淨驗證（2026-10-24）

證據目錄：`evidence/er_epr_20261023T170011Z_lakebuild/`。

- 全新目錄、依 manifest 抓依賴、`lake exe cache get`、11 個逐步 `lake build --wfail`（含 `ErEpr.NoGo`、`ErEpr.Chain`）與最後完整 `lake build --wfail`，全部 rc=0。
- 公理：`rc_axioms=0`，146 條全部只依賴標準三公理。
- manifest 三次 sha256 相同；9 個套件 HEAD 與 manifest 相符；節點上的原始碼 sha256 與 repo 相符。
- 節點空閒，等待 0 秒即開跑。

## B2 KMS 線（2026-10-24，Opus 5.5 實作、主線驗收）

證據目錄：`evidence/er_epr_20261023T175412Z_b2_final/`。

### 正式結果

- 結果：rc=0，14 個模組與根檔都沒有錯誤，也沒有警告。
- 公理：187 條定理全部只依賴標準三公理（原 146 + 新 41）。全庫無 `set_option`、無 `sorry`。
- 檔案 sha256（其餘檔不變）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/TFD.lean` | b9f79f09dc8114d016af892082378db706dd77b8fd5e80f4a6df4c5b8521aee6 |
| `ErEpr/KMS.lean` | e1137c6869bac5baa4068d7630514e41c7eb19898623a99e940044607b49350d |
| `ErEpr/KMSPair.lean` | 1c209dcce61f09038085cb151c4dcee02744a4b5bc4819ca7af6c2ae86700cf4 |
| `ErEpr/Axioms.lean` | 0a35338ab7a5234d73d81b330a2c983d9d1efded26e30ea9e6e51d4b88e5998b |
| `ErEpr.lean` | c1d7748190155fd7f375036e237da3d83a650b82a5971dce65dcac02609b97b9 |

- 中途：iter1、iter2 只紅在 `no_ringHom_matrix_to_comm`（`single` 的索引被推成 ℕ），iter3 起全綠。

### 新增

- **S1**（`TFD.lean`）：`tfdAmp_eq_exp`、`exp_half_mul_conjTranspose`、`tfdAmp_mul_conjTranspose'`、`tfdAmp_isUnit`、`negctrl_tfdAmp_full_beta`。
- **S3**（`TFD.lean`）：`vecOf_mul`、`purification_unique_of_isUnit`、`tfd_purification_unique`、`tfdAmpWrong_eq`、`eigU_mul_transpose_unitary`、`vecOf_tfdAmpWrong`。
- **S2**（`KMS.lean`）：`nuStep`（ν_β(b) = e^{−βH} b e^{βH}）、`nuStepAlgHom`、`IsKMS`（tr(σ a ν b) = tr(σ b a)）、`gibbs_isKMS`、`kms_core`、`isKMS_unique`、`isKMS_iff_eq_gibbs`、`gibbs_transpose`、`tfd_ptrB_isKMS`、`tfd_ptrA_isKMS`、`negctrl_scalar_not_kms`、`negctrl_maxMixed_not_kms`。
- **S4**（`KMSPair.lean`）：`KMSPair`（ν、ω、ω_one、nondeg、kms）、`tracial_iff_period`、`ofComm`、`gibbsState`、`gibbs_isUnit`、`gibbsKMSPair`、`gibbs_tracial_iff_scalar`、`negctrl_diag_not_tracial`、`negctrl_gibbs_not_tracial`、`negctrl_nondeg_needed`、`no_ringHom_matrix_to_comm`。

### 反向演習

| 演習 | 改動 | 證據目錄 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|---|
| E1 | `tfdAmp_eq_exp` 的 β/2 改 β | `…175154Z_drill_E1` | `tfdAmp_eq_exp`、`tfdAmp_mul_conjTranspose'` | **為假**，主庫 `negctrl_tfdAmp_full_beta` 正面證明 |
| K1 | `IsKMS` 拿掉 ν（改恆等） | `…175157Z_drill_K1` | `gibbs_isKMS`、`isKMS_unique` | **為假**，副本內 example：(1/2)•1 滿足而 ≠ gibbs |
| K2 | `isKMS_unique` 拿掉 tr σ = 1 | `…175200Z_drill_K2` | `isKMS_unique`、`isKMS_iff_eq_gibbs` | **為假**，副本內 example：σ = 0 |
| P1 | 拿掉 `IsUnit M` | `…175203Z_drill_P1` | `purification_unique_of_isUnit`、`tfd_purification_unique` | 只證明證明跑不過（方陣版其實靠極分解為真，未在 Lean 證） |
| T1 | 刪 `nondeg` 欄位 | `…175206Z_drill_T1` | `tracial_iff_period` 的 → 方向、`gibbsKMSPair` | **為假**，副本內 example：ℂ×ℂ、ν(x,y) = (x,x) |

副本的 diff 行數大於「一處」（9–21 行），因為 Opus 在副本裡**另加了 example** 來正面證明改壞的陳述為假；主線核對過，被改壞的定義／陳述都只有一處。

### 主線驗收紀錄

- 對照最終證據：全模組 rc=0；187/187；各檔 sha256 與工作樹相符；`set_option` 0、`sorry` 0。
- 親讀 `nuStep`、`IsKMS` 定義：符號與簡報約定一致（ν_β(b) = e^{−βH} b e^{βH}；tr(σ a ν b) = tr(σ b a)），Gibbs 代入檢查主線先前已手算。
- 親讀 `isKMS_unique`（比規格強：不需 Hermitian、不需非空）、`KMSPair` 五欄位、`tracial_iff_period` 證明體、`gibbs_tracial_iff_scalar`、`purification_unique_of_isUnit`、`no_ringHom_matrix_to_comm` 陳述。沒有削弱。
- Opus 超出明列範圍改了 `tools/lake_build_node.sh` 的逐步清單（加 KMS、KMSPair）；這是必要的，主線保留。

## B2 後的 lake build 乾淨驗證（2026-10-24）

證據目錄：`evidence/er_epr_20261023T175714Z_lakebuild/`。

- 全新目錄、依 manifest 抓依賴、`lake exe cache get`、13 個逐步 `lake build --wfail`（含 `ErEpr.KMS`、`ErEpr.KMSPair`）與最後完整 `lake build --wfail`，全部 rc=0。
- 公理：`rc_axioms=0`，187 條全部只依賴標準三公理。
- manifest 三次 sha256 相同；9 個套件 HEAD 與 manifest 相符；節點上的原始碼 sha256 與 repo 相符。

## B3 ER 側接縫 ＋ B4 圖對態的約束（2026-10-24，Opus 5.5 實作、主線驗收）

證據目錄：`evidence/er_epr_20261023T190752Z_b34_final/`。

### 正式結果

- 結果：rc=0，16 個模組與根檔都沒有錯誤，也沒有警告。
- 公理：271 條，其中 268 條只依賴標準三公理，3 條**不依賴任何公理**（`cutInd_submod`、`mmi_contract`、`mmi_boundary`，全由 `decide` 證）。全庫無 `set_option`、無 `sorry`。
- 檔案 sha256（其餘檔不變）：

| 檔案 | sha256 |
|---|---|
| `ErEpr/Charts.lean` | c0ccac71d65f9e56e2ca36bb1a113ff04127f98c7210aab869921cdd035c0b8c |
| `ErEpr/MinCut.lean` | 450bcef77b863eff159d47ec1a965510c6c80d96aaddf8ddc797ca56f6900b0d |
| `ErEpr/Axioms.lean` | 0885ef74151bf71354cf85b7e74fe70397b061a694ea77cd21c61e8ba0505a57 |
| `ErEpr.lean` | 6d71dbc750cddbceaa88d087e1777cfbaf7bf91ddd42d5bbf7ed9b45ac54375d |

### 新增（84 條）

- **Charts.lean（53 條）**：K1 `kf_strictMonoOn`、`kf_two_M`、`FK_mul_kf`、`FK_mul_deriv_sqrt_kf`、`FS_rOfRho`、`hasDerivAt_rOfRho`、`confIso_eq_rOfRho`、`areaIso_eq_rOfRho`；曲線層級 `kruskal_pullback`（方向 (t, r) ↦ (U, V)，只在右外區）；K1′ `sliceX_inv`、`sliceX_sq`、`hasDerivAt_sliceX`、`FK_mul_deriv_sliceX_sq`、`inversion_swaps_UV`（約定 (U, V) = (−X, X)，讓 ρ > M/2 落在 `RightExterior`）；K2 `boost_preserves_prod`、`boost_metric`、`futureCausal_boost`、三區保持、`negctrl_boost_spacelike`；K4 `r_gt_of_slice`、`r_lt_of_timelike`、`r_eq_at_bifurcation`、`area_lt_area_iff`、`area_slice_gt`、`area_timelike_lt`、`negctrl_interior_area`。
- **MinCut.lean（31 條）**：G6 `cutEdges_card_submodular`、`cutEdges_compl`；G5 `minCut`（ℕ 的 `sInf`，所有定理假設 X ⊆ bd）、`minCut_le`、`exists_minCut`、收縮映射 `mmiA/B/C/ABC`（y_A = x_AB ∧ x_AC ∧ ¬x_BC 等）、`mmi_contract`（64 情形 decide）、`mmi_boundary`、`minCut_mmi`；GHZ `regionState_eq_ptrB_reindex`（保真）、`regionState_ghz`、`regionEntropy_ghz`、`ghz4_mmi_fails`、`ghz4_not_minCut`；G1 `rank_le_one_iff_vecMulVec`（改名避免撞 mathlib 的 `rank_le_one_iff`）、G2 `tnAmp_product_of_no_cut`、`negctrl_product_with_bond`、G4 `rank_cutMat_eq_of_inj_surj`。

### 反向演習

| 演習 | 改動 | 證據目錄 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|---|
| C1 | 16M² → 8M² | `…190236Z_drill_C1` | `FK_mul_kf`、`kruskal_pullback` | 為假（副本 example：M=1、r=3） |
| C2 | M²/4ρ → M²/2ρ | `…190239Z_drill_C2` | `sliceX_inv`、`inversion_swaps_UV` | 為假（M=ρ=1） |
| C3 | boost 改 (e^λU, e^λV) | `…190242Z_drill_C3` | `boost_preserves_prod`、`boost_metric`、`futureCausal_boost_of` | 為假（λ=1、U=V=1） |
| M1 | 次模 ≤ 改 ≥ | `…190254Z_drill_M1` | `cutEdges_card_submodular` | 為假（路徑圖，decide） |
| M2 | MMI 反向 | `…190601Z_drill_M2b`（`…190421Z_drill_M2` 是副本輔助引理寫錯的一次，保留） | `minCut_mmi`、`ghz4_not_minCut` | 對 min-cut 為假（四葉星形圖）；同一反向式對 GHZ 熵成立，正好展示兩者分離 |
| G2 | 秩 1 改 2 | `…190422Z_drill_G2` | `rank_le_one_iff_vecMulVec` 及兩個依賴它的定理 | ⇒ 方向為假（2×2 單位矩陣） |

**限定**：
- 演習副本的 diff 除了被改壞的那一處，還含正面反例的 example，以及**兩處後來才改的 docstring／檔頭**（`Charts.lean` 的 `kf_strictMonoOn` docstring、`MinCut.lean` 的檔頭）：演習是在最終版前一步的文字上跑的，被改壞的定義／陳述與最終版相同，但副本不是最終版的逐位元複本。
- MMI 收縮映射「是唯一解」這件事是 Python 窮舉的，沒有在 Lean 證；Lean 證的是它**滿足**收縮性與邊界條件（這就夠用）。
- `kruskal_pullback` 只做 (t, r) ↦ (U, V) 方向、只在右外區。

### 主線驗收紀錄

- 對照最終證據：全模組 rc=0；268/271 標準三公理、3 條零公理；各檔 sha256 與工作樹相符；`set_option` 0、`sorry` 0。
- 親讀 `minCut` 定義（`sInf`，X ⊆ bd 假設）、`minCut_mmi` 陳述（A、B、C ⊆ bd 且兩兩不交）、收縮映射與 `mmi_contract`（主線另外手驗邊界條件：v ∈ A 時三位元 (1,0,1) ↦ y_A = 1、y_B = y_C = 0）、`ghz4_mmi_fails` 與 `ghz4_not_minCut` 陳述、`kruskal_pullback`、`inversion_swaps_UV`。沒有削弱。
- 親讀六份演習的 diff 首行，確認每份被改壞的定義／陳述只有一處。

## B3＋B4 後的 lake build 乾淨驗證（2026-10-24）

證據目錄：`evidence/er_epr_20261023T191143Z_lakebuild/`。

- 全新目錄、依 manifest 抓依賴、`lake exe cache get`、15 個逐步 `lake build --wfail`（含 `ErEpr.Charts`、`ErEpr.MinCut`）與最後完整 `lake build --wfail`，全部 rc=0。
- 公理：`rc_axioms=0`，271 條中 268 條只依賴標準三公理，3 條不依賴任何公理。
- manifest 三次 sha256 相同；9 個套件 HEAD 與 manifest 相符；節點上的原始碼 sha256 與 repo 相符。

## 收尾衛生＋S5 便宜半段（2026-10-24）

主線（Opus 5.5）直接做、直接驗。探針證據：`evidence/er_epr_20261024T061605Z_s5c_iter1/`（S5 綠、耦合第一版全紅）、`…062016Z_coup_iter2/`（閉包修好，一條真缺口）、`…062147Z_coup_iter3/`（全綠）。

### S5（`NoGo.lean` 檔尾）

- `energyMean`（⟨H⟩ = N/Z）、`trace_gibbs_mul_self`（tr(gibbs·H) = ⟨H⟩，保真）、`hasDerivAt_energyMean`（dE/dβ = −Var）、`gibbs_dS_eq_beta_dE`（dS/dβ = β·dE/dβ）、`gibbs_entropy_energy_slope`（Var ≠ 0 時兩導數之比 = β）。
- 演習 S5（−Var 改 +Var）：`hasDerivAt_energyMean`、`gibbs_dS_eq_beta_dE` 都紅。
- **限定**：這是同一個**定義**（β = 熵對能量的斜率）在兩側都成立，ER 側是 `first_law_area` 的假設、EPR 側是定理；不是同一個**值**。值對不上由 `no_finite_dim_gibbs_matches_bh` 負責。Klein 不等式那一半沒做。

### 耦合檢驗機械化（`ErEpr/Coupling.lean`）

- 依賴閉包：從定理出發，遞迴展開型別與證明體裡的 `ErEpr.*` 常數，mathlib 不展開。`#assert_uses` 要求閉包含錨點；`#assert_not_uses` 要求不含，且閉包裡除了自己還要至少有一條定理，否則判「不可信」而紅。根檔 import 它，斷言隨 `lake build --wfail` 一起檢查。
- **第一版是壞的**：用 `ConstantInfo.value?` 取證明體，對定理取到 `none`（不報錯），閉包只展開型別。結果所有 `#assert_uses` 紅、所有 `#assert_not_uses` **假綠**（s5c_iter1）。改成直接對 `ConstantInfo` 分情形取值後，16 條裡 15 條通過（coup_iter2）。
- **機械檢查抓到一條原先說錯的依賴**：`ghz4_not_minCut` 沒有用到 `ghz4_mmi_fails`；它直接用 `regionEntropy_ghz` 重算，兩者是平行證明。原斷言是看原始碼猜的。已改成 `ghz4_not_minCut ⇒ minCut_mmi regionEntropy_ghz mmi_contract`、`ghz4_mmi_fails ⇒ regionEntropy_ghz`，並加反向斷言 `ghz4_not_minCut ⇏ ghz4_mmi_fails`。最終 18 條斷言全過。
- 這也解除 B0＋B1 一節的限定（「耦合定理依賴 `hawking_beta` 只由原始碼可見，沒有用 `getUsedConstants` 機械驗」）：現在 `no_gibbs_matches_first_law ⇒ hawking_beta first_law_area …` 是機械斷言。
- 耦合檢驗本身的演習：CP1（加一條假的獨立性斷言）、CP2（加一條假的依賴斷言）、CP3（重現第一版的閉包錯誤）、CP4（對證明體裡沒有其他定理的 `ptrB_apply` 做獨立性斷言）全紅；CP3 連 `#assert_not_uses antitoneOn_gibbsEntropyFn` 也被空洞守門判紅。

### 反向演習一鍵重跑

- 清單 `tools/drills_manifest.json`（47 份）由 `tools/drills_extract.py` 產生：每份歷史演習的副本，與它演習前最後一次綠燈探針的副本逐行比對，抽出改動與「改壞後為假」的反例區塊；`tools/drills_finalize.py` 再手挑必須紅的宣告（取自本檔各節演習表）、重新指定 R17、加 BASE（不改、必須全綠）、S5、CP1–CP4。每筆改動必須在現行檔案裡剛好出現一次。
- R17 重新指定：原目標 `Tendsto … (𝓝 1) ↔ β = 8πM` 在 B0 改寫成 `UnitConeAngle M β ↔ β = 8πM`，與 COUPLE 同一處；R17 改打 `conicalRatio_tendsto` 的極限值（β/8πM → β/4πM）。
- 重跑結果：`evidence/drills_20261024T062754Z/REPORT.md`，**47/47 通過**（BASE 綠；其餘每份 rc ≠ 0、必須紅的宣告都紅；有反例區塊的 K1、K2、C1、C2、C3、M1、M2b、G2，反例區塊全綠，也就是「改壞後的陳述為假」這次重新被確認）。冒煙測試 `evidence/drills_20261024T062627Z/`（BASE、R1、K1、CP4，4/4）。

**限定**：
- 紅名單只看第一個失敗模組（`run_probe.sh` 在那裡停）；下游模組的連帶紅不在表內。COUPLE 這類跨模組的依賴改由耦合斷言機械檢查。
- 這次全量重跑用的是舊版跑者：演習樹在輪到時才複製。跑的途中改過的只有 `ErEpr/Axioms.lean`（補印 70 條）與根檔 `ErEpr.lean`（加 import Coupling）；只有 BASE 會編到這兩個檔，而 BASE 在第一批、改檔之前就複製好了。跑者之後已改成開跑前一次建好全部樹，並在報告裡記原始碼快照 sha256。
- T1 的反例區塊在原檔中段，被當成一般改動（不是 append），跑者沒有單獨檢查它綠；紅名單裡沒有它（只有 `tracial_iff_period`、`gibbsKMSPair`），所以它是綠的，但這是看紅名單推的，不是跑者的判定。
- 其餘演習的限定（只證「證明跑不過」者）照各節原文，重跑不改變它們。

### 定理索引與公理覆蓋

- `docs/THEOREM_INDEX.md` 由 `tools/gen_index.py` 從磁碟產生：每條 `theorem`／`lemma` 的位置、公理狀態、指定與實際紅的演習、耦合斷言。
- **產生時發現的更正**：原始碼裡 `theorem` 宣告 345 條（S5 前 341 條），`Axioms.lean` 只印了 275 條。先前各節寫的「271 條」是印出來的條數，不是全庫定理數；另 70 條輔助引理（多半是 `_apply`、線性性小引理）從沒被機械查過公理。主定理用到它們時，公理已含在主定理的輸出裡，但沒被用到的就沒查過。已全部補印（用 `ErEpr.` 全名，避免 `open ErEpr` 下撞名）。結果見下一節 lake build。

## 收尾後的 lake build 乾淨驗證（2026-10-24）

證據目錄：`evidence/er_epr_20261024T063448Z_lakebuild/`（由新腳本 `tools/lake_build_remote.sh` 推送、執行、收回；第一次跑時它用 scp 大括號收檔失敗，改成 ssh＋tar 後手動補收，腳本已修）。

- 全新目錄、依 manifest 抓依賴、`lake exe cache get`、16 個逐步 `lake build --wfail`（新增 `ErEpr.Coupling`）與最後完整 `lake build --wfail`，全部 rc=0。
- 耦合斷言在 lake build 裡執行（`lake_build_ErEpr.Coupling.log` 有 18 行「通過」）；另以 `lake env lean` 單獨重跑一次，`rc_coupling=0`、18 條通過、0 錯誤。
- 公理：`rc_axioms=0`，**345 條**中 342 條只依賴標準三公理，3 條不依賴任何公理（`cutInd_submod`、`mmi_contract`、`mmi_boundary`）。補印的 70 條輔助引理全部是標準三公理以內。
- manifest 三次 sha256 相同；節點上 17 個原始碼檔的 sha256 與工作樹逐一相符。
- 定理索引 `docs/THEOREM_INDEX.md` 由這份 `axioms.out` 產生：345 條，非「標準三公理／零公理」0 條，沒被印公理的 0 條。

## S5 的 Klein 那一半（2026-10-24）

主線（Opus 5.5）直接做、直接驗。新檔 `ErEpr/Klein.lean`，22 條定理。探針：`evidence/er_epr_20261024T065128Z_klein_iter1/`～`…065332Z_klein_iter3/`（三輪：rw 方向、`RCLike.ofReal` 與 `Complex.ofReal` 的轉型、`haveI` 風格 linter）、`…065606Z_klein_wired/`（接上根檔、耦合、公理列印後全綠）。

### 定理

- `vnEntropy_le_beta_energy_add_log`：PSD、跡 1 的 σ 滿足 S(σ) ≤ β·tr(σH) + log Z。
- `vnEntropy_eq_beta_energy_add_log_iff`：等號 ⇔ σ = gibbs H β。
- `vnEntropy_gibbs_eq_beta_energy_add_log`、`vnEntropy_le_gibbs_of_energy_eq`、`vnEntropy_lt_gibbs_of_energy_eq`（最大熵，唯一）。
- 中間層：`trace_mul_eq_sum`（tr(σH) = Σ p_i E_j |W_ij|²，保真）、`sum_normSq_row`／`_col`（雙隨機）、`klein_sum_identity`、`klein_real`、`klein_gap_eq`、`kleinGap_nonneg`／`_pos`。
- 負控制：`negctrl_klein_pure_H2`（|0⟩⟨0| 嚴格小於，CHAIN_DESIGN 指定的那一個）、`negctrl_klein_other_beta_H2`（β′ = −ln 2 的 Gibbs 態在 β = ln 2 下嚴格小於）。

### 耦合斷言（新增 4 條，全庫 22 條全過）

- 不等式 ⇒ `klein_gap_eq kleinGap_nonneg vnEntropy_eq_sum_eigenvalues trace_mul_eq_sum`；
- 等號情形 ⇒ `gibbs_eq_conj vnEntropy_gibbs_eq_fn trace_gibbs_mul_self kleinGap_pos`；
- 不等式 **⇏** `vnEntropy_gibbs_eq_fn hawking_beta first_law_area`：不等式不經 Gibbs 熵閉式，所以「S(gibbs) = βE + log Z」由兩條獨立路線各得一次（B1 的閉式、Klein 的等號情形）；也不碰 ER 側；
- `negctrl_klein_pure_H2` ⇒ `vnEntropy_eq_beta_energy_add_log_iff gibbs_H2_log2`。

### 反向演習（KL1–KL5）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| KL1 | 右邊減 1 | 主定理、兩條最大熵推論、兩個負控制 | **為假**（反例區塊：Gibbs 態取等號，`H2`、β = ln 2） |
| KL2 | 逐項缺口 (p − q) 改 (q − p) | `kleinGap_nonneg`、`kleinGap_pos`、`klein_sum_identity` | **為假**（反例區塊：p = 0、q = 1 得 −1） |
| KL3 | 拿掉 tr σ = 1 | 主定理與下游 | 只證證明跑不過 |
| KL4 | 等號情形改成 σ = gibbs H (2β) | 等號定理與下游 | 只證證明跑不過 |
| KL5 | 雙隨機恆等式拿掉行和 | `klein_sum_identity`、`klein_real` | 只證證明跑不過 |

全量重跑：`evidence/drills_20261024T065721Z/REPORT.md`，**51/52**（這次用新版跑者，開跑前一次建好全部樹，報告記原始碼快照 sha256）。唯一不過的是 KL1：**反例區塊本身寫錯**（把 σ 寫成 `_`，Lean 推不出來），跑者因此判它紅——這正是「反例區塊必須綠」那條判準該抓的情況。改成明寫 `gibbs H2 (Real.log 2)` 後單獨重跑 BASE＋KL1：`evidence/drills_20261024T070502Z/`，2/2。其餘 50 份（含 41 份歷史演習、S5、CP1–CP4、KL2–KL5）在 51/52 那一次就通過。

### lake build

`evidence/er_epr_20261024T070616Z_lakebuild/`：17 個逐步 `lake build --wfail`（新增 `ErEpr.Klein`）與完整 `lake build --wfail` 全部 rc=0；公理 367 條，364 條標準三公理、3 條零公理（同前）；耦合 22 條通過、0 錯誤；manifest 三次 sha256 相同；18 個原始碼檔 sha256 與工作樹逐一相符。`docs/THEOREM_INDEX.md` 由這份 `axioms.out` 重產：367 條，非標準 0、未印 0。

**限定**：
- 不等式是有限維、固定 H 的陳述。它是 Landauer 與 Casini 形式 Bekenstein 界共同的數學核心（`docs/TRIANGLE.md` §2），但兩個界本身沒有在本庫證明。
- 負控制只在 2×2 上；一般維度的「非 Gibbs 態嚴格小於」由等號定理給出，不另做數值見證。

## 三角的便宜磚 T-a、T-b、T-e（2026-10-24）

主線直接做、直接驗。新檔 `ErEpr/Triangle.lean`，10 條定理。探針：`evidence/er_epr_20261024T074217Z_tri_iter1/`（`norm_num` 先展開 `H2`，`gibbs_H2_log2` 套不上）、`…074342Z_tri_iter2/`（綠）、`…074554Z_tri_wired/`（接上根檔、耦合、公理列印後全綠）。

- **T-a**：`bekensteinBound_throat`（r(M/2) = 2M、E = M ⇒ 2πRE = A/4）、`first_law_saturates_bekenstein`；負控制 `negctrl_bekenstein_isotropic_radius`（用 ρ = M/2 當半徑只得 A/16）。
- **T-b**：`reservoir_entropy_le_beta_heat`（ΔS ≤ β·ΔE）、`reservoir_entropy_eq_beta_heat_iff`（等號 ⇔ 終態是同溫 Gibbs 態）、`landauer_reservoir_bit`（ΔS ≥ ln 2 ⇒ ΔE ≥ ln 2/β）；負控制 `negctrl_reservoir_not_gibbs`（起點是 β′ = −ln 2 的 Gibbs 態時，熵不變而能量減少 1/3，不等式失敗）。
- **T-e**：`hasDerivAt_bh_energy_of_entropy`（沿 S = 4πM²，dE/dS = 1/(8πM)）、`bh_landauer_saturated`（單位錐角條件下 dE/dS = 1/β）。
- **耦合斷言**（新增 6 條，全庫 28 條全過）：T-b ⇒ Klein 兩條、⇏ ER 側；T-a ⇒ `first_law_area rOfRho_throat throat_area_eq`、⇏ Klein；T-e ⇒ `hawking_beta`、⇏ Klein。

### 反向演習（TA1、TB1、TB2、TE1）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| TA1 | Bekenstein 界的 2π 改 π | `bekensteinBound_throat` | **為假**（反例區塊：M = 1 時 2π ≠ 4π） |
| TB1 | ΔS ≤ βΔE 改 ≥ | `reservoir_entropy_le_beta_heat`、`landauer_reservoir_bit` | **為假**（反例區塊：終態 \|0⟩⟨0\|，由 Klein 的嚴格版） |
| TB2 | 拿掉終態半正定 | 同上 | 只證證明跑不過 |
| TE1 | dE/dS 的 8πM 改 4πM | `hasDerivAt_bh_energy_of_entropy`、`bh_landauer_saturated` | 只證證明跑不過 |

全量重跑 `evidence/drills_20261024T074717Z/REPORT.md`：**56/56**（新版跑者、原始碼快照 sha256 記在報告裡）。TA1 沒有讓 `first_law_saturates_bekenstein` 變紅：它只是把 `bekensteinBound_throat` 改寫進來，陳述形式不變。

### lake build

`evidence/er_epr_20261024T075659Z_lakebuild/`：18 個逐步 `lake build --wfail`（新增 `ErEpr.Triangle`）與完整 build 全部 rc=0；公理 377 條，374 條標準三公理、3 條零公理（同前）；耦合 28 條通過、0 錯誤；manifest 三次相同；19 個原始碼檔 sha256 逐一相符。索引重產：377 條，非標準 0、未印 0。

**限定**：T-a 是代數恆等式（半徑取面積半徑是約定），T-a 與 T-e 繼承 `first_law_area`／`hawking_beta` 的假設；T-b 只是完整 Landauer 的熱庫那一半。本庫沒有證 Bekenstein 界，也沒有證 Landauer 原理。

## T-c 模哈密頓量與相對熵（2026-10-24）

主線直接做、直接驗。新檔 `ErEpr/Modular.lean`，13 條定理。探針：`evidence/er_epr_20261024T082933Z_mod_iter1/`（`log_div` 要先展開 `bw`；`diagonal_add` 方向）、`…083107Z_mod_iter2/`（`diagonal_add` 是逐點 lambda 形式，用定義相等的 `have` 轉接）、`…083248Z_mod_iter3/`（綠）、`…083504Z_mod_wired/`（接線後全綠）。

- 保真：`exp_neg_modHamOf`（exp(−K) = U·diag(q)·Uᴴ）、`gibbs_modHamOf`（ρ₀ = gibbs K 1）、`partZ_modHamOf`（Z = 1）、`modHamOf_gibbs`（Gibbs 參考態的 K = βH + log Z）、`relEntropyOf_diagonal`（對角時 = 古典 KL 散度）。
- 主定理：`entropy_le_modular`（ΔS ≤ Δ⟨K⟩）、`entropy_eq_modular_iff`（等號 ⇔ σ = ρ₀）、`relEntropyOf_nonneg`、`relEntropyOf_eq_zero_iff`、標準形 `entropy_le_modHam`（只要 ρ₀ 正定）。
- 負控制：`negctrl_modular_not_fullRank`（q = (1, 0) 時 K = 0，最大混合態的 ΔS = ln 2 > 0 = Δ⟨K⟩）。
- 耦合斷言新增 4 條（全庫 32 條全過）：`entropy_le_modular ⇒ reservoir_entropy_le_beta_heat gibbs_modHamOf exp_neg_modHamOf`、`relEntropyOf_nonneg ⇒ vnEntropy_le_beta_energy_add_log partZ_modHamOf`、`entropy_le_modular ⇏ hawking_beta first_law_area`、`modHamOf_gibbs ⇒ eigU_spectral`。

### 反向演習（TC1–TC3）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| TC1 | K 的 −log 改 +log | `modHamOf_isHermitian`、`exp_neg_modHamOf`、`modHamOf_gibbs`、`relEntropyOf_diagonal` | 只證證明跑不過 |
| TC2 | 拿掉 q > 0 | `entropy_le_modular`、`entropy_le_modHam` | 拿掉後的特例為假，由主庫的 `negctrl_modular_not_fullRank` 證明（不是演習副本裡的反例區塊） |
| TC3 | 古典 KL 的 log p − log q 對調 | `relEntropyOf_diagonal` | 只證證明跑不過 |

全量重跑 `evidence/drills_20261024T083639Z/REPORT.md`：**59/59**。

### lake build

`evidence/er_epr_20261024T084755Z_lakebuild/`：19 個逐步 `lake build --wfail`（新增 `ErEpr.Modular`）與完整 build 全部 rc=0；公理 390 條，387 條標準三公理、3 條零公理（同前）；耦合 32 條通過、0 錯誤；manifest 三次相同；20 個原始碼檔 sha256 逐一相符。索引重產：390 條，非標準 0、未印 0。

**限定**：只到 ΔS ≤ Δ⟨K⟩，是 Casini 論證的有限維骨架；Bisognano–Wichmann 與 Δ⟨K⟩ ≤ 2πRE 不在本庫，Bekenstein 界沒有證。K 依賴所選的對角化，「不同對角化給出同一個 K」未證。

## 糾纏第一定律，對易情形（2026-10-24）

主線直接做、直接驗。新檔 `ErEpr/FirstLaw.lean`，11 條定理。探針：`evidence/er_epr_20261024T085855Z_fl_iter1/`（section 變數要 `omit`；`comp_of_eq` 參數順序）、`…090027Z_fl_iter2/`（`omit` 不能放在 docstring 後；`congr_deriv` 的目標要由 `refine` 決定）、`…090157Z_fl_iter3/`（綠）、`…090418Z_fl_wired/`（接線後全綠）。

- 主定理 `entanglement_first_law_diag`：ρ₀ = diag(q)（q > 0）、保跡方向 v（Σv = 0），d/dt S(diag(q + tv))|₀ = d/dt tr(diag(q + tv)·K)|₀，K = −log ρ₀。
- 第一條路（直接微分）：`hasDerivAt_entropy_diagPath`（δS = Σ v(−log q − 1)）、`hasDerivAt_modEnergy_diagPath`（δ⟨K_r⟩ = Σ v(−log r)，任何參考 r）。
- 第二條路（極小值）：`first_law_of_relEntropy_min`：只假設兩邊在 0 可微，用 T-c 的 D ≥ 0 與 D(ρ₀) = 0 推出導數相等。
- `relEntropy_diagPath_pos`：v ≠ 0、t ≠ 0 時 D > 0（一階相等、二階嚴格）。
- 負控制 `negctrl_first_law_wrong_reference`：q = (1/2, 1/2)、v = (1, −1) 時 δS = 0，而 r = (2/3, 1/3) 的模哈密頓量給 δ⟨K_r⟩ = −ln 2。
- 耦合斷言新增 5 條（全庫 37 條全過），其中兩條獨立性斷言：第一條路**不**用相對熵與 Klein；第二條路**不**用第一條路的任何導數計算，也不用主定理。兩條路是真的互相獨立。

### 反向演習（FL1–FL3，都附反例區塊）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| FL1 | 拿掉 Σv = 0 | `entanglement_first_law_diag` | **為假**（q = (1/2, 1/2)、v = (1, 1)：兩邊差 Σv = 2） |
| FL2 | 第二條路的結論改成 S′ = K′ + 1 | `first_law_of_relEntropy_min` | **為假**（反例用第一條路的主定理） |
| FL3 | 負控制的參考換回同一個 (1/2, 1/2) | `negctrl_first_law_wrong_reference` | **為假**（反例就是第一定律本身） |

全量重跑 `evidence/drills_20261024T090545Z/REPORT.md`：**62/62**。

### lake build

`evidence/er_epr_20261024T091627Z_lakebuild/`：20 個逐步 `lake build --wfail`（新增 `ErEpr.FirstLaw`）與完整 build 全部 rc=0；401 條定理全數以 `#print axioms` 查過，398 條只依賴標準三公理（`propext`、`Classical.choice`、`Quot.sound`），3 條不依賴任何公理（同前）；全庫沒有 `axiom` 宣告、沒有 `sorry`。耦合 37 條通過、0 錯誤；manifest 三次相同；21 個原始碼檔 sha256 逐一相符。

**用詞更正**：先前各節寫的「公理 N 條」意思是「N 條定理查過公理」，不是用了 N 條公理。全庫用到的公理自始至終只有上面三條。

**限定**：只做對易（對角）情形；一般擾動需要固有值的一階微擾，沒有做。本庫沒有 RT 公式與幾何動力學，所以沒有任何關於 Einstein 方程的陳述。

## 不對易的糾纏第一定律：影子的存在性（2026-10-24）

先評估（不動手）：mathlib 沒有固有值導數、矩陣函數導數、固有值連續性。改走夾擠路線，核心不等式 D ≤ tr((σ−ρ₀)²)/q_min 先用 numpy 驗過（scratchpad `fl_check.py`：3000 組隨機不對易例子零違反；中央差分的 δS 與 tr(δρK) 差距隨 h² 下降）。數值驗證只是動手前的探路，不是證據；證據是下面的 Lean。

新檔 `ErEpr/FirstLawGeneral.lean`，20 條定理。探針：`evidence/er_epr_20261024T095423Z_flg_iter1/`（`(t : ℂ)` 標註把綁定變數推成複數、`field_simp` 已收掉目標、`convert` 鑽進 instance 等五處）、`…095627Z_flg_iter2/`（綠）、`…095902Z_flg_wired/`（接線後全綠）。

- **存在性與導數**：`hasDerivAt_entropy_gibbsPath`（任何 Gibbs 參考態、任何無跡 Hermitian X：t ↦ S(G + tX) 在 0 可微，導數 β·tr(XH)）、`entanglement_first_law`（任何滿秩 ρ₀：導數 tr(XK)，K = −log ρ₀）。
- **夾擠的零件**：`kleinGap_le_sq`（g(p, q) ≤ (p−q)²/q）、`sum_sq_doubly_stochastic`、`trace_mul_self_eq_sum`、`trace_gibbs_mul_self_eq_sum`、`trace_mul_gibbs_eq_sum`、`trace_sub_gibbs_sq_eq_sum`（Σ|W|²(p−q)² = tr((σ−G)²)）、`klein_gap_le_sq`（D ≤ tr((σ−G)²)/c）、`exists_gibbs_lower`。
- **路徑仍是態**：`gibbs_sub_smul_one_posSemidef`、`eventually_smul_one_add_posSemidef`、`eventually_gibbsPath_posSemidef`（Loewner 序拆解，沒有用複數二次型）。
- **第二條路**：`first_law_gibbs_of_hasDerivAt`（只假設可微，極小值論證）。
- **交叉驗證**：`first_law_general_agrees_diag`（對易時一般公式等於 `FirstLaw.lean` 直接微分的值，由導數唯一性）。
- **負控制**：`negctrl_first_law_not_fullRank`（參考態 (1, 0) 不滿秩，沿 diag(1 − t/2, t/2) 熵在 0 不可微）。
- **耦合斷言**新增 6 條（全庫 43 條全過），其中三條獨立性：夾擠那條路⇏對易版直接微分與極小值那條路；極小值那條路⇏夾擠與二次上界；`entanglement_first_law`⇏ER 側。

### 反向演習（FG1–FG4）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| FG1 | 逐項上界收緊成 (p−q)²/(2q) | `kleinGap_le_sq`、`klein_gap_le_sq` | **為假**（p = 0、q = 1：1 ≤ 1/2） |
| FG2 | 拿掉 tr X = 0 | `hasDerivAt_entropy_gibbsPath`、`entanglement_first_law` | 只證證明跑不過 |
| FG3 | 導數改成 2β·tr(XH) | 同上 | **為假**（反例用極小值那條路：H2、β = ln 2、X = diag(1, −1)） |
| FG4 | 負控制的參考改成滿秩 (1/2, 1/2) | `negctrl_first_law_not_fullRank` | **為假**（對易版直接給出可微：影子存在） |

全量重跑 `evidence/drills_20261024T100038Z/REPORT.md`：**65/66**。唯一沒過的是 FG3：反例區塊的陳述裡綁定名 `hH` 沒被引用，linter 在 warningAsError 下報錯，跑者因此判反例區塊紅——又一次是反例寫法問題，不是定理問題。改成 `_` 後單獨重跑 BASE＋FG3：`evidence/drills_20261024T101303Z/`，2/2。

### lake build

`evidence/er_epr_20261024T101439Z_lakebuild/`：21 個逐步 `lake build --wfail`（新增 `ErEpr.FirstLawGeneral`）與完整 build 全部 rc=0；421 條定理全數查過公理，418 條只用標準三公理、3 條零公理；無 `axiom` 宣告、無 `sorry`；耦合 43 條通過、0 錯誤；manifest 三次相同；22 個原始碼檔 sha256 逐一相符。索引重產：421 條，非標準 0、未印 0。

**限定**：有限維、直線路徑 G + tX、一階。沒有 RT 公式與幾何動力學，所以沒有任何關於 Einstein 方程的陳述。

## X₁′ 類比重力的核心定理（2026-10-24）

主線直接做、直接驗。開工前探 mathlib：只有實數速率的 Gamma 積分，沒有複數速率版本；有參數積分微分與解析函數唯一性定理。

新檔兩個，17 條定理。探針：`evidence/er_epr_20261024T103006Z_unruh_iter1/`～`…104029Z_unruh_iter6/`（GammaRotation 第二輪綠；Unruh 第六輪綠）、`…104312Z_unruh_wired/`（接線後全綠）。

### `ErEpr/GammaRotation.lean`（純分析）

- `integral_gammaKernel`：Re a > 0、Re r > 0 ⇒ ∫₀^∞ t^{a−1}e^{−rt} dt = (1/r)^a Γ(a)。
- 證法：`differentiableAt_gammaIntegral`（積分號下微分，控制函數 t^{Re a}e^{−(Re r₀/2)t}）⇒ 右半平面上解析；(1/r)^a Γ(a) 也解析；兩者在正實軸上由 mathlib 的實數版相等；右半平面凸所以連通；唯一性定理（`eqOn_of_preconnected_of_frequently_eq`，用實數列 1 + 1/(n+1) → 1 給「頻繁相等」）。

### `ErEpr/Unruh.lean`

- `bogoliubov_ratio_regularized`：‖∫x^{a−1}e^{−(δ−ik)x}‖/‖∫x^{a−1}e^{−(δ+ik)x}‖ = exp(−2Ω·arg(δ+ik))，a = ε + iΩ，ε > 0、δ > 0，**k 任意**（第五輪 linter 指出 k > 0 沒用到，照實拿掉）。與 ε 無關。
- `bogoliubov_ratio_tendsto`：δ → 0⁺ 時 → e^{−πΩ}（k > 0，arg(ik) = π/2）；`bogoliubov_ratio_sq_tendsto`：Ω = ω/κ 時平方 → e^{−2πω/κ}。
- `meanOccupation_eq`：Boltzmann 加權平均 Σn e^{−βωn}/Σe^{−βωn} = 1/(e^{βω} − 1)；`bogoliubov_thermal`：B = e^{−2πω/κ}A、A − B = 1 ⇒ B = 平均佔據數（逆溫度 2π/κ）。
- `hasDerivAt_FS_horizon`、`surfaceGravity_schwarzschild`（κ = 1/(4M)）、`unitConeAngle_of_surfaceGravity`（β = 2π/κ 滿足單位錐角條件）、`bogoliubov_factor_schwarzschild`（熱因子 e^{−8πMω}）。
- 負控制：`negctrl_bogoliubov_fermi`（A + B = 1 得 Fermi–Dirac，且 ≠ 玻色佔據數）、`negctrl_no_horizon`（κ → 0⁺ 時熱因子 → 0）。
- 耦合斷言新增 6 條（全庫 49 條全過）：Bogoliubov 那條鏈用到複數 Gamma 積分；係數比⇏ER 側；**熱分佈⇏Bogoliubov 計算**（防 CHAIN_DESIGN §10 指出的空洞：熱不是用係數比定義的）；**表面重力⇏`hawking_beta`、`conicalRatio_tendsto`**（兩條溫度路線獨立）；兩路一致的定理⇒兩者。

### 反向演習（U1–U6）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| U1 | 平均佔據數 −1 改 +1 | `meanOccupation_eq` 與下游 | 只證證明跑不過 |
| U2 | 對易關係 A − B = 1 改 A + B = 1 | `bogoliubov_thermal` | **為假**（反例用費米負控制） |
| U3 | κ = 1/(4M) 改 1/(2M) | `hasDerivAt_FS_horizon` 與下游 | 只證證明跑不過 |
| U4 | 視界極限 e^{−πΩ} 改 e^{−2πΩ} | `bogoliubov_ratio_tendsto` 與下游 | 只證證明跑不過 |
| U5 | 無視界極限 0 改 1 | `negctrl_no_horizon` | 只證證明跑不過 |
| U6 | 複數 Gamma 積分 (1/r)^a 改 r^a | `integral_gammaKernel` | **為假**（反例用 mathlib 的實數版：a = 1、r = 2 時 1/2 ≠ 2） |

全量重跑 `evidence/drills_20261024T104451Z/REPORT.md`：**72/72**，反例區塊第一次就全綠。

### lake build

`evidence/er_epr_20261024T105841Z_lakebuild/`：23 個逐步 `lake build --wfail`（新增 `ErEpr.GammaRotation`、`ErEpr.Unruh`）與完整 build 全部 rc=0；438 條定理全數查過公理，435 條只用標準三公理、3 條零公理；無 `axiom`、無 `sorry`；耦合 49 條通過、0 錯誤；manifest 三次相同；24 個原始碼檔 sha256 逐一相符。索引重產：438 條，非標準 0、未印 0。

**限定**：
- 「這兩個積分就是 Rindler 與 Minkowski 模態的 Bogoliubov 係數（差一個共同歸一化）」是物理設定，只寫在說明文字裡。
- |α|² − |β|² = 1 是假設，沒有從 Klein–Gordon 內積推出。
- 熱態沒有用 `IsKMS`（有限維矩陣）寫，改用獨立定義的諧振子平均佔據數；這是偏離 CHAIN_DESIGN §10 設計稿的地方。
- 只做 1+1 維、單一模態；沒有灰體因子、沒有反作用。實驗（Steinhauer、Weinfurtner）量的是這一層運動學，但本庫沒有任何實驗數據或比對。


## T-d 完整 Landauer（2026-10-24）

先評估（不動手）：mathlib 有 Kronecker 積的工具（`diagonal_kronecker_diagonal`、`mul_kronecker_mul`、`conjTranspose_kronecker`、`trace_kronecker`）與 `Real.negMulLog_mul`，也有 `PosSemidef.kronecker`；沒有 von Neumann 熵，自然也沒有次可加性。評估估 450–650 行、15–30 輪；使用者選「兩段一起做」。

新檔 `ErEpr/Landauer.lean`，481 行、36 條定理。探針：`evidence/er_epr_20261024T115020Z_landauer_iter1/`（第一輪只紅在 linter：未用的 section 變數、`tendsto_finset_sum` 改名為 `tendsto_finsetSum`、多餘的 simp 參數，以及一個 2×2 乘法被 simp 化成 `ᵥ*` 沒算完）、`…115224Z_landauer_iter2/`（綠）、`…115602Z_landauer_wired/`（接上耦合與公理檔後全綠）。

- **A 側部分跡**：`trace_ptrA_mul`（對偶刻畫）、`ptrA_kronecker`、`trace_ptrA`、`ptrA_posSemidef`。
- **Kronecker 與么正**：`star_kronecker`、`kronecker_star_mul`、`kronecker_mul_star`、`kronU`／`coe_kronU`。
- **張量積可加**：`kronecker_spectral`（兩組固有分解的 Kronecker 積是 ρ⊗σ 的固有分解）、`vnEntropy_kronecker`（S(ρ⊗σ) = S(ρ) + S(σ)）。
- **次可加性**：`modHamOf_kronecker`（乘積參考態的 K = K_A⊗1 + 1⊗K_B）、`trace_mul_modHamOf_of_eq`、`vnEntropy_le_marginal_cross`（相對熵 ≥ 0 拆成兩個邊際）、`mixUnif`／`mixUnif_pos`／`sum_mixUnif`（(1−ε)a + ε/d 滿秩且和為 1）、`tendsto_mul_log_mixUnif`（逐項極限，a = 0 的項恆為 0）、`vnEntropy_le_of_marginal_spectral`、`vnEntropy_subadditive`（邊際態不必滿秩）。沒有用到固有值對矩陣的連續性。
- **Landauer**：`landauer`（S(ρ_S) − S(ρ′_S) ≤ β·(tr(ρ′_R H) − tr(γH))）、`landauer_bit`（一個位元至少 ln 2/β）、`no_heatless_erasure`（熱庫不吸熱，系統熵不降）。
- **見證**：`swapU` 與四條交換引理、`landauer_swap_witness`（最大混合 qubit 與 β = ln 2 的熱庫交換：系統熵嚴格減少、熱庫吸熱 1/6）、`vnEntropy_gibbs_H2_log2_lt`（log 3 − (2/3)log 2 < log 2，即 27 < 32）。
- **負控制**：`resetS_not_unitary`、`resetS_conj_mix2`、`negctrl_landauer_not_unitary`（非么正重置不放熱就把最大混合態變純態）；`negctrl_subadditive_unnormalized`（ρ = 2·1 時次可加性失敗）。
- **耦合斷言**新增 7 條（全庫 56 條全過）：`landauer` 用到四塊；次可加性用到相對熵與兩側部分跡、**不經** T-b 與 `entropy_le_modular`；張量積可加性**不經** Klein；`landauer` ⇏ ER 側；見證與負控制各接到自己的計算。

### 反向演習（LD1–LD4）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| LD1 | 次可加性拿掉跡為 1 | `vnEntropy_subadditive`、`landauer` | **為假**（反例：`negctrl_subadditive_unnormalized`） |
| LD2 | 熱的正負號反過來 | `landauer` 與兩個推論 | **為假**（反例：交換見證，系統熵降、熱庫吸熱） |
| LD3 | 拿掉么正性 | `landauer` 與兩個推論 | **為假**（反例：`negctrl_landauer_not_unitary`） |
| LD4 | 參考態只縮不混（拿掉 ε/d） | `mixUnif_pos`、`sum_mixUnif`、`vnEntropy_le_of_marginal_spectral` | **為假**（a = 0 時 (1−ε)·a = 0，不滿秩） |

全量重跑 `evidence/drills_20261024T115752Z/REPORT.md`：**76/76**，反例區塊第一次就全綠。演習的原始碼快照比最終版早一步：之後只改了 `ErEpr/Triangle.lean` 的說明文字（「完整 Landauer 本庫沒有做」改成指向本檔），沒有改任何宣告。

### lake build

`evidence/er_epr_20261024T120025Z_lakebuild/`：24 個逐步 `lake build --wfail`（新增 `ErEpr.Landauer`）與完整 build 全部 rc=0；474 條定理全數查過公理，471 條只用標準三公理、3 條零公理；無 `axiom`、無 `sorry`；耦合 56 條通過、0 錯誤；manifest 三次相同；25 個原始碼檔 sha256 逐一相符（含改過說明文字的 `Triangle.lean`）。

**限定**：
- 有限維；熱庫起點恰為 Gibbs 態；系統與熱庫起點是乘積態（相關起點的反例是下一批）。
- 「熱」定義為熱庫的能量增量；系統的哈密頓量、做功、總能量守恆都不在定理裡。
- 等號情形（準靜態）沒有刻畫；Reeb–Wolf 的有限尺寸加強版沒有做。

## 糾纏的起點（2026-10-24）

使用者指定：相關（糾纏）起點的 Landauer 負控制，加上 Bell 態的 S(AB) = 0 < S(A)，用同一個解糾纏的么正矩陣。新檔 `ErEpr/Correlated.lean`，24 條定理。探針：`evidence/er_epr_20261024T122238Z_corr_iter1/`（多餘 simp 參數；`omit [DecidableEq ι]` 省掉了實際用到的實例）、`…122420Z_corr_iter2/`（綠）、`…122656Z_corr_wired/`（接線後全綠）。

- **解糾纏矩陣**：`bellK`（Bell 基底的整數矩陣，對稱）、`star_bellK`、`bellK_mul_self`（K² = 2）、`bellK_conj_maxEnt`（K·Bell·K = 2|00⟩⟨00|）、`sBell_mul_self_complex`、`disentangle`（D = K/√2）、`star_disentangle`、`disentangle_mul_self`、`disentangle_star_mul`、`disentangle_conj_maxEnt`（D·Bell·Dᴴ = |0⟩⟨0| ⊗ |0⟩⟨0|）、`maxEnt_eq_disentangle_conj`。逐格計算全在整數矩陣 K 上，√2 只在 (1/√2)² = 1/2 出現。
- **Bell 態**：`vnEntropy_bell`（S(AB) = 0，走 D、么正不變與張量積可加）、`vnEntropy_ptrB_bell`、`vnEntropy_ptrA_bell`（S(A) = S(B) = ln 2）、`bell_conditional_entropy`（S(AB) − S(B) = −ln 2）、`bell_mutual_information`（2 ln 2）、`negctrl_entropy_monotone`（S(A) ≤ S(AB) 失敗）。
- **古典對照**：`negMulLog_sum_le`、`vnEntropy_ptrB_diagonal_le`（對角聯合分佈滿足 S(A) ≤ S(AB)）。
- **乘積假設拿不掉**：`gibbs_zero_ham`（H = 0 的 Gibbs 態是最大混合態）、`product_start_no_erasure`（`no_heatless_erasure` 的推論）、`ptrA_bell_eq_gibbs`、`ptrB_bell_eq_mix2`、`ptrB_disentangle_bell`、`correlation_is_fuel`（邊際態相同，乘積起點不能降熵、Bell 起點一步歸零）、`negctrl_landauer_correlated`（`landauer` 的形狀：系統熵減少 ln 2 > 0 = β·Q）。
- **耦合斷言**新增 6 條（全庫 62 條全過）：S(Bell) = 0 用到 D、張量積可加、么正不變，**不經**秩上界；負控制**不經** `landauer` 與次可加性（反例獨立算出）；`correlation_is_fuel` 兩邊都接上（`landauer` 與 D）；古典對照**不經** Bell 與次可加性。

### 反向演習（BL1–BL3）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| BL1 | Bell 基底矩陣拿掉負號 | `bellK_mul_self`、`bellK_conj_maxEnt` | **為假**（(00, 11) 那一格是 2 不是 0） |
| BL2 | 「乘積起點不能抹除」的起點換成 Bell 態 | `correlation_is_fuel` | **為假**（解糾纏一步歸零） |
| BL3 | 古典的 S(A) ≤ S(AB) 推廣到任何量子態 | `vnEntropy_ptrB_diagonal_le` | **為假**（Bell 態：ln 2 > 0） |

全量重跑 `evidence/drills_20261024T122850Z/REPORT.md`：**79/79**，反例區塊第一次就全綠。

### lake build

`evidence/er_epr_20261024T122910Z_lakebuild/`：25 個逐步 `lake build --wfail`（新增 `ErEpr.Correlated`）與完整 build 全部 rc=0；498 條定理全數查過公理，495 條只用標準三公理、3 條零公理；無 `axiom`、無 `sorry`；耦合 62 條通過、0 錯誤；manifest 三次相同；26 個原始碼檔 sha256 逐一相符。

**限定**：只有一個 2×2 的例子；沒有證「相關起點時 Landauer 的修正項是互資訊」這類一般陳述；H = 0 讓熱恆為 0，負控制的內容全在系統的熵能不能降。

## 觀測＝把線轉給儀器（2026-10-24）

起點是使用者「被觀測時線條脫落」的直覺；主線拆成兩半，使用者指定做可證的那一半（退相干）。新檔 `ErEpr/Measurement.lean`，19 條定理。探針：`evidence/er_epr_20261024T125354Z_meas_iter1/`（`Kraus` 在 `NoSignalling.lean`，沿 Landauer 那條 import 鏈沒有帶進來；多餘 simp 參數）、`…125543Z_meas_iter2/`（綠）、`…125752Z_meas_wired/`（接線後全綠）。

- **態與測量**：`plusProj`（|+⟩⟨+|）與 `plusProj_isHermitian`、`plusProj_mul_self`、`plusProj_posSemidef`、`trace_plusProj`；`cnot` 與 `star_cnot`、`cnot_mul_self`、`cnot_star_mul`；`cnot_measure`（CNOT(|+⟩⟨+| ⊗ |0⟩⟨0|)CNOTᴴ = Bell）；`ptrB_before`、`ptrB_after`。
- **只看系統**：`measurement_dephases`（干涉項 1/2 → 0，對角不變）、`measurement_entropy`（系統 0 → ln 2，整體 0 → 0）。
- **交叉檢查**：`vnEntropy_plusProj`（秩一，S(AB) = S(BA) 換成 1×1，不經 Bell）、`measurement_total_entropy_conserved`（整體熵前後相同）。
- **只動一端解不開**：`ptrB_local_conj`（當時在 Fin 2 上逐格算的 Tr_B((U⊗1)X(U⊗1)ᴴ) = U·Tr_B X·Uᴴ；2026-10-25 推廣到任意維度）、`local_cannot_undo`、`pointer_cannot_undo`（沿用 `Kraus.no_signalling`）。
- **兩端一起才解得開**：`joint_undo`（D 讓系統回純態；再一次 CNOT 完全還原，干涉項回到 1/2）。
- **負控制**：`negctrl_local_no_decoherence`（不糾纏的交互作用，系統熵仍是 0）。
- **耦合斷言**新增 7 條（全庫 69 條全過）：只動系統那條**不經**不可通訊、只動儀器那條**不經** `ptrB_local_conj`，兩條路互不依賴；測量前的 0 **不經** Bell 與解糾纏矩陣。

### 反向演習（MS1–MS3）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| MS1 | CNOT 的控制位元反過來 | `cnot_measure` | **為假**（得到 Ψ⁺，(00, 00) 那一格是 0 不是 1/2） |
| MS2 | 宣稱只動系統就能讓熵回到 0 | `local_cannot_undo` | **為假**（U = 1 時熵是 ln 2） |
| MS3 | 宣稱只動儀器就能讓熵回到 0 | `pointer_cannot_undo` | **為假**（Pauli X 通道之後熵仍是 ln 2） |

全量重跑 `evidence/drills_20261024T125949Z/REPORT.md`：**82/82**，反例區塊第一次就全綠。

### lake build

`evidence/er_epr_20261024T130031Z_lakebuild/`：26 個逐步 `lake build --wfail`（新增 `ErEpr.Measurement`）與完整 build 全部 rc=0；517 條定理全數查過公理，514 條只用標準三公理、3 條零公理；無 `axiom`、無 `sorry`；耦合 69 條通過、0 錯誤；manifest 三次相同；27 個原始碼檔 sha256 逐一相符。

**限定**：2×2 玩具，一個系統 qubit、一個儀器 qubit、一次交互作用；「坍縮」只代表系統的約化態變成對角，不談詮釋，也沒有定義觀測者；`ptrB_local_conj` 是 Fin 2 上逐格算的，不是一般維度的引理；沒有環境中多個 qubit 的退相干速率，也沒有指針基底的選擇。

## 糾纏的一夫一妻（2026-10-24）

先評估再動手：mathlib 有 `trace_mul_conjTranspose_self_eq_zero_iff`、`PosSemidef.trace_eq_zero_iff`、`dotProduct_mulVec_zero_iff`；ρ = BᴴB 的分解在 mathlib 要走 C*-代數的 scoped 實例，改用本庫的固有分解自造。評估 250–300 行、3–6 輪。新檔 `ErEpr/Monogamy.lean`，258 行、16 條定理。探針：`evidence/er_epr_20261024T134028Z_mono_iter1/`（只有一個未用的 section 變數）、`…134221Z_mono_iter2/`（綠）、`…134505Z_mono_wired/`（接線後全綠）。

- **半正定那一步**：`exists_eq_conjTranspose_mul_self`（ρ = BᴴB，B = √D·Uᴴ）、`mul_eq_zero_of_trace_mul_eq_zero`（ρ ≥ 0、R 是 Hermitian 投影、tr(ρR) = 0 ⇒ ρR = 0）。
- **秩一投影**：`rankOne_mul_self`、`rankOne_conjTranspose`、`trace_rankOne`；區塊計算 `rankOne_kron_one_conj`。
- **主定理**：`monogamy`（AB 的邊際是 c·|v⟩⟨v| ⇒ ρ_ABC = ρ_AB ⊗ ρ_C）。
- **三方記帳**：`ptrMid`、`ptrMid_kronecker`、`ptrMid_kronecker3`（保真：跡掉的是中間那一個）；`monogamy_mutualInfo`（ρ_AC = ρ_A ⊗ ρ_C，互資訊 0）。
- **Bell 實例**：`maxEnt_posSemidef`、`trace_maxEnt`、`bell_rankOne_norm`、`bell_monogamy`（I(A:B) = 2 ln 2、I(A:C) = 0）、`bell_monogamy_witness`（假設可滿足：Bell ⊗ |0⟩⟨0|）。
- **負控制**：`negctrl_monogamy_mixed`（邊際不是純態時整體不是乘積）。
- **耦合斷言**新增 5 條（全庫 74 條全過）：主定理**不經** Klein 與相對熵；負控制**不經**主定理與半正定那一步。

### 反向演習（MG1–MG3）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| MG1 | 拿掉「AB 的邊際是純態」 | `monogamy` 與下游 | **為假**（反例：`negctrl_monogamy_mixed`） |
| MG2 | 宣稱 Bell 時 I(A:C) = 2 ln 2 | `bell_monogamy` | **為假**（Bell ⊗ \|0⟩⟨0\| 時是 0） |
| MG3 | 區塊計算裡 v、w 對調 | `rankOne_kron_one_conj`、`monogamy` | 只證證明跑不過 |

全量重跑 `evidence/drills_20261024T134707Z/REPORT.md`：**85/85**，反例區塊第一次就全綠。

### lake build

第一次 `evidence/er_epr_20261024T134728Z_lakebuild/` **失敗**：節點磁碟 100% 滿，`lake exe cache get` 就報 `No space left on device`，後面的步驟沒有跑。原因是這兩天的 20 個乾淨 lake build 工作目錄（各約 7.7 GB，共 135 GB）從沒清過。經使用者同意刪掉這 20 個目錄（證據早已收回本機），磁碟降到 44%；`tools/lake_build_remote.sh` 改成收回證據後自動清掉節點上本次的工作目錄。

重跑 `evidence/er_epr_20261024T142013Z_lakebuild/`：27 個逐步 `lake build --wfail`（新增 `ErEpr.Monogamy`）與完整 build 全部 rc=0；533 條定理全數查過公理，530 條只用標準三公理、3 條零公理；無 `axiom`、無 `sorry`；耦合 74 條通過、0 錯誤；manifest 三次相同；28 個原始碼檔 sha256 逐一相符；節點工作目錄已自動清除。

**限定**：只證「邊際是純態 ⇒ 與第三方完全不相關」；量化的一夫一妻（CKW 不等式、squashed entanglement）沒有做；防火牆悖論只出現在說明文字裡。

## 糾纏交換（2026-10-24）

先評估再動手（使用者選全套，含四結果平均）。新檔 `ErEpr/Swapping.lean`，315 行、28 條定理。探針：`evidence/er_epr_20261024T151253Z_swap_iter1/`（求和次序；`Fin 2` 的 `1 + 1` 沒被化簡；`ptrBC_swapVec` 超出 heartbeat）、`…151549Z_swap_iter2/`（加 `fin_two_one_add_one` 後只剩超時）、`…151843Z_swap_iter3/`（先證 `star_swapVec`，再拆成四個 16 格的引理，綠）、`…152150Z_swap_wired/`（接線後全綠）。

- **記帳**：`mutualInfo`、`mutualInfo_kronecker`、`ptrBC`、`ptrBC_kronecker`（保真：Tr_BC(X_AB ⊗ Y_CD) = Tr_B X ⊗ Tr_C Y）、`ptrBC_smul`、`trace_ptrBC`、`vecMulVec_kronecker`。
- **起點與投影**：`bellPairVec`、`bellPair_eq`（Bell ⊗ Bell = (1/4)|ψ⟩⟨ψ|）、`fin_two_one_add_one`（只用 propext）、`bellSign`、`swapProj`、`swapVec`、`swapProj_mulVec`（核心一行）、`vecMul_swapProj`、`swap_post`、`star_swapVec`、`ptrBC_swapVec_00`～`_11`、`ptrBC_swapVec`、`bellAD`、`trace_bellAD`、`bellAD_zero`、`ptrBC_swap_post`、`swap_prob`（每個結果機率 1/4）。
- **交換前後**：`swap_before`（A–D 乘積、互資訊 0）、`entanglement_swapping`（機率 1/4、歸一化後 A–D = Bell、互資訊 0 → 2 ln 2）。
- **不能傳訊息**：`swap_average_eq`、`swap_average_no_signalling`（四結果平均 = 交換前）。
- **負控制**：`sepProj`、`sepVec`、`sepProj_mulVec`、`vecMul_sepProj`、`ptrBC_sepVec`、`negctrl_swap_separate`（各自量：A–D 乘積、互資訊 0）。
- **耦合斷言**新增 5 條（全庫 79 條全過）：平均那條**不經**交換定理；負控制**不經** Bell 投影。

### 反向演習（SW1–SW3）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| SW1 | B、C 的投影拿掉「聯合」條件 | `swapProj_mulVec` 與下游 | 只證證明跑不過 |
| SW2 | 宣稱 Φ⁺ 結果機率 1/2 | `entanglement_swapping` | **為假**（`swap_prob`：1/4） |
| SW3 | 宣稱四結果平均之後 A–D 是 Bell 態 | `swap_average_no_signalling` | **為假**（(00, 11) 那一格是 0 不是 1/2） |

全量重跑 `evidence/drills_20261024T152446Z/REPORT.md`：**88/88**，反例區塊第一次就全綠。

### lake build

`evidence/er_epr_20261024T152507Z_lakebuild/`：28 個逐步 `lake build --wfail`（新增 `ErEpr.Swapping`）與完整 build 全部 rc=0；561 條定理全數查過公理，557 條用到標準三公理、1 條只用 propext（`fin_two_one_add_one`）、3 條零公理；無 `axiom`、無 `sorry`；耦合 79 條通過、0 錯誤；manifest 三次相同；29 個原始碼檔 sha256 逐一相符；節點工作目錄已自動清除。`ErEpr.Swapping` 那一步的峰值記憶體 7.3 GB（探針的單檔 `lean -M 8192` 是 6.9 GB），是全庫最重的一步。

**限定**：四個 qubit、一次 Bell 測量，寫成「投影＋事後挑選」；當時沒有證 Π² = Π（論證只用到 Π|ψ⟩；2026-10-25 補上，見最後一節）；「各自量」的負控制只有 |0⟩|0⟩ 一個結果，沒有一般的 LOCC 定理；「接蟲洞」只在說明文字裡。

## 上游對照與總覽（2026-10-24）

使用者要求先收斂：暫停加新模組、查上游、整理總覽。淺層 clone Physlib（`a6395db`，含 2026 年 3 月併入的 Lean-QuantumInfo）與 Lean-Quantum（`bf1c4f6`）到草稿區，只讀不編譯，按名字與關鍵字對照。結果寫在 `docs/OVERVIEW.md` §3：Physlib 已有 von Neumann 熵、次可加性、**強次可加性**（無 `sorry`）、相對熵與 DPI；ER 側、不可能定理、KMS 共享結構與今天幾塊上游沒有；mathlib 沒有複數速率的 Gamma 積分。限定：不是逐行比對。

## 洞的形狀：AMPS 矛盾與不可能定理的負控制（2026-10-25）

使用者在收斂階段指定補兩塊（先評估再動手）。都加在既有模組；兩塊第一輪就編綠。探針：`evidence/er_epr_20261024T171627Z_shape_iter1/`（綠）、`…171937Z_shape_wired/`（接上公理與耦合後全綠）。

**AMPS（`ErEpr/Swapping.lean`，13 條）**
- 記帳：`ptrFirst`（跡掉三方的第一個）、`ptrFirst_kronecker`、`ptrFirst_kronecker3`（保真）。
- `amps_monogamy`（A–B 純態 ⇒ ρ_BR = ρ_B ⊗ ρ_R、I(B:R) = 0）、`amps_contradiction`（A–B = Bell 與 I(B:R) = 2 ln 2 不能同時成立）。
- 見證：`ampsUnitaryState`、`ampsUnitaryState_posSemidef`、`ptrFirst_ampsUnitaryState`、`amps_each_half_satisfiable`（兩個要求各自可滿足）。
- 負控制：`ghzState`、`ghzState_posSemidef`、`ptrFirst_ghzState`、`ptrB_ptrFirst_ghzState`、`ptrA_ptrFirst_ghzState`、`mutualInfo_ptrFirst_ghzState`、`negctrl_amps_mixed`（GHZ：A–B 不是 Bell，I(B:R) = ln 2 > 0）。

**不可能定理的負控制（`ErEpr/NoGo.lean`，6 條）**
- `twoTierDist`、`sum_twoTierDist`、`sum_negMulLog_twoTierDist`、`exists_twoTier_entropy`（中間值定理）、`exists_hamiltonian_gibbs_entropy_eq`（任何 0 < s < log(n+2)、β ≠ 0：有 H 使 S(gibbs H β) = s）。
- `negctrl_nogo_varying_hamiltonian`（同一個維度，每個 β ∈ (a, b) 各有 H_β 對上 β²/16π）、`nogo_hinges_on_fixed_hamiltonian`（∃H ∀β 為假、∀β ∃H 為真）。

**耦合斷言**新增 6 條（全庫 85 條全過）：AMPS 用到一夫一妻；GHZ 負控制**不經**一夫一妻；不可能定理的負控制**不經**單調性證明與不可能定理本身。

### 反向演習（AF1、NG5、NG6）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| AF1 | AMPS 拿掉「A–B 是純態」 | `amps_monogamy` | **為假**（GHZ：I(B:R) = ln 2） |
| NG5 | 量詞換成「∃ 一個固定的 H 對所有 β」 | `negctrl_nogo_varying_hamiltonian` | **為假**（就是不可能定理） |
| NG6 | 拿掉 β ≠ 0 | `exists_hamiltonian_gibbs_entropy_eq` | **為假**（β = 0 時熵固定是 log 2） |

全量重跑 `evidence/drills_20261024T172219Z/REPORT.md`：**91/91**，反例區塊第一次就全綠。

### lake build

`evidence/er_epr_20261024T172239Z_lakebuild/`：28 個逐步 `lake build --wfail` 與完整 build 全部 rc=0；580 條定理全數查過公理，576 條用到標準三公理、1 條只用 propext、3 條零公理；無 `axiom`、無 `sorry`；耦合 85 條通過、0 錯誤；manifest 三次相同；29 個原始碼檔 sha256 逐一相符；節點工作目錄已自動清除。

**限定**：AMPS 是「恰好純態」的理想化版本，不是原始用強次可加性的量化論證；不可能定理的負控制只說「H 固定」是關鍵假設，不說隨質量變的 Hilbert 空間就是黑洞的正確描述。`NoGo.lean`、`Swapping.lean` 開頭的結果清單這次沒有更新（新定理各自有說明文字）。

## 補兩個缺口：Π 是投影、只動系統的引理推廣到任意維度（2026-10-25）

使用者指定補 DESIGN §25、§27 自己列出的兩個缺口。都改在既有模組。探針：`evidence/er_epr_20261024T181102Z_proj_iter1/`（`Measurement` 綠、`Swapping` 只剩 `sum_swapProj`）、`…181346Z_proj_iter2/`（全綠）、`…181659Z_proj_wired/`（接上公理與耦合後全綠）。

**只動系統（`ErEpr/Measurement.lean`）**
- `ptrB_local_conj`：任意有限維 ι、κ，Tr_B((U ⊗ 1)X(U ⊗ 1)ᴴ) = U·Tr_B X·Uᴴ（原本只在 Fin 2 上逐格算）。下游 `local_cannot_undo`、`joint_undo`、`negctrl_local_no_decoherence` 不必改。

**Π 是投影（`ErEpr/Swapping.lean`，9 條）**
- B、C 上的 Bell 投影：`star_bellSign`、`bellVecBC`、`bellProjBC`、`bellVecBC_norm`、`bellProjBC_mul_self`、`bellProjBC_conjTranspose`、`sum_bellProjBC`（Σ_st |β_st⟩⟨β_st| = 1）。
- 重排：`swapReindex : ((a, b), (c, d)) ↦ ((a, d), (b, c))`、`swapProj_eq_reindex`（Π_st = (1_{AD} ⊗ |β_st⟩⟨β_st|) 重排）。
- 結論：`swapProj_isHermitian`、`swapProj_mul_self`（Π² = Π）、`sum_swapProj`（Σ Π_st = 1）。

**耦合斷言**新增 3 條（全庫 88 條全過）：Π² = Π 用到重排與 `rankOne_mul_self`，**不經** `swapProj_mulVec` 與 `entanglement_swapping`；完備性用到重排與 `sum_bellProjBC`。

### 反向演習（SWP1、LOC1）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| SWP1 | B、C 上的投影少了 1/2 | `bellProjBC_mul_self`、`sum_bellProjBC`（連帶 `swapProj_eq_reindex`） | **為假**（(00, 00) 那一格：P² 是 2，P 是 1） |
| LOC1 | 約化公式把 U 與 Uᴴ 對調 | `ptrB_local_conj` 與下游 | 只證證明跑不過 |

全量重跑 `evidence/drills_20261024T182708Z/REPORT.md`：92/93。沒過的是 SWP1，而且錯在**清單**不在證明：我把「必須紅」寫成 `bellVecBC_norm`，但那條是 (1/2)·Σ = 1，不依賴 `bellProjBC` 的定義，改它本來就不會紅；實際紅的是下游三條，反例區塊是綠的。改正清單後單獨重跑 `evidence/drills_20261024T185634Z/REPORT.md`：1/1。兩次用的是同一份原始碼快照（`4b09c2dd…`）。

### lake build

`evidence/er_epr_20261024T182145Z_lakebuild/`：28 個逐步 `lake build --wfail` 與完整 build 全部 rc=0；589 條定理全數查過公理，585 條用到標準三公理、1 條只用 propext、3 條零公理；無 `axiom`、無 `sorry`；耦合 88 條通過、0 錯誤；manifest 三次相同；29 個原始碼檔 sha256 逐一相符；節點工作目錄已自動清除。`ErEpr.Swapping` 那一步峰值 7.4 GB（上一批 7.3 GB）。

**限定**：Bell 測量仍只在兩個 qubit（B、C）上；沒有 d 維的最大糾纏基底；`swap_average_no_signalling` 沒有改用完備性重寫。

## 面積律：熵版的 ∀ 割上界（2026-10-25）

使用者同意「補完面積律這一塊就停數學、轉去準備公開」。一維（MPS）的熵版上界與等號早就有（T3a、T3b）；這次是任意圖、任意頂點子集的版本，加在 `ErEpr/TensorNetwork.lean`（改成 import `ErEpr.Entropy`）。探針：`evidence/er_epr_20261024T191537Z_area_iter1/`（只缺 `open scoped ComplexOrder` 與一個 `haveI`）、`…191642Z_area_iter2/`（全綠）、`…191957Z_area_wired/`（接上公理與耦合後全綠）。

**新定理（10 條）與定義**
- 定義 `cutEntropy`（割 W 的糾纏熵，不另外歸一化）、`evalZero`、`evalOne`、`parEnds`、`parEdge`、`parTN`、`parC`。
- 主定理 `cutEntropy_tnAmp_le`：歸一化之後，S(W) ≤ 割邊數 × log D。
- 共用計算：`cutMat_diag`、`cutMat_diag_mul_conjTranspose`、`trace_cutMat_diag`、`cutEntropy_diag`（振幅 c·[x₀ = x₁] 的割：約化態是最大混合態，熵 log(dim)）。
- 等號見證：`card_cutEdges_par`、`tnAmp_parTN`、`parC_mul_self`、`area_law_saturated`（k 條平行邊、任何 k 與 D > 0：已歸一，熵恰為 k log D）。
- 負控制：`negctrl_nonlocal_entropy`（非局域網路歸一之後，割邊數 0、熵 log 2）。

**耦合斷言**新增 3 條（全庫 91 條全過）：主定理用到 `rank_cutMat_tnAmp_le` 與 `vnEntropy_le_log_rank`；等號見證與負控制都**不經**主定理與秩上界（熵是直接算出來的）。

### 反向演習（AL1、AL2）

| 演習 | 改動 | 紅在哪裡 | 改壞後的陳述 |
|---|---|---|---|
| AL1 | 拿掉「割邊數」那個因子（熵 ≤ log D） | `cutEntropy_tnAmp_le` | **為假**（兩條平行邊、D = 2：已歸一，熵 2 log 2 > log 2） |
| AL2 | 拿掉歸一化假設 | `cutEntropy_tnAmp_le` | 只證證明跑不過（一般矩陣的反例是 `Entropy.lean` 的 `negctrl_unnormalized`） |

全量重跑 `evidence/drills_20261024T192240Z/REPORT.md`：**95/95**，反例區塊都綠。原始碼快照 `2d9e4337…`。

### lake build

`evidence/er_epr_20261024T195146Z_lakebuild/`：28 個逐步 `lake build --wfail` 與完整 build 全部 rc=0；599 條定理全數查過公理，595 條用到標準三公理、1 條只用 propext、3 條零公理；無 `axiom`、無 `sorry`；耦合 91 條通過、0 錯誤；manifest 三次相同；29 個原始碼檔 sha256 逐一相符，與演習快照是同一份原始碼；節點工作目錄已自動清除。`ErEpr.TensorNetwork` 那一步峰值 6.8 GB；最重的仍是 `ErEpr.Swapping`（7.4 GB）。

**限定**：只有上界（RT「≤」那一半）；等號見證是平行邊這一族，不是一般圖；沒有最小割＝熵、沒有隨機張量網路、沒有任何幾何或愛因斯坦方程的陳述。

