# 把「複數速率 Gamma 積分」送成 mathlib PR — 操作步驟（全部由你本人執行）

前提：GitHub 帳號 bally65 已 fork `leanprover-community/mathlib4`（之前兩個 PR 已有 fork）。

以下在一個**乾淨的** clone 裡做（不要用 `~/.cache` 那棵驗證用的 checkout）。
git 若被 Xcode 授權擋，前面加 `DEVELOPER_DIR=/Library/Developer/CommandLineTools`。

```bash
cd ~/mathlib4-pr                      # 之前 Fibonacci 那個 PR 用的 clone；沒有的話照舊 clone 自己的 fork
git fetch upstream master
git checkout -b gamma-complex-rate upstream/master
git apply ~/Documents/alloy/er_epr_lean/upstream/mathlib-gamma-complex-rate/gamma-complex-rate.patch
lake exe cache get
lake build --wfail Mathlib.Analysis.SpecialFunctions.Gamma.Beta   # 期望：Build completed successfully，零 warning
lake exe runLinter Mathlib.Analysis.SpecialFunctions.Gamma.Beta  # 期望：Linting passed
git add Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean
git commit -m "feat(Analysis/SpecialFunctions/Gamma): Gamma integral with a complex rate"
git push -u origin gamma-complex-rate
```

（`lake build` 會重編 `Beta.lean` 與它的依賴；在 Mac 上跑會吃 CPU，若要避開，可以只做 `git apply` → commit → push，讓 GitHub 的 CI 去編。節點上已經在同一個 master 上編過，收據在 `master_check/`。）

然後到 GitHub 開 PR（base: `leanprover-community/mathlib4:master`），標題與內文貼 `PR_DESCRIPTION.md`（`# Title` 底下那行是標題，`# Body` 底下是內文；`<!-- -->` 那行註解不要貼）。

建議順序
1. 開 PR 前再搜一次 open PRs（關鍵字 `cpow_mul_exp_neg_mul`、`complex rate`），確認這兩天沒人送同一件事。
2. 可以先在 Zulip `#Is there code for X?` 問一聲；之前兩個 PR 沒有先問也沒問題，看你。
3. AI 聲明：照之前 #44019、#44020 的做法，你寫中文原意、附英文翻譯並註明翻譯由 Claude 協助；開 PR 後加 `LLM-generated` 標籤。

備註
- patch 是對 master `280e9fcd660f4d566d97adf0b821c49b4eee91b6`（2026-10-24）產生的（見 `BASE_COMMIT.txt`）；
  若 upstream/master 已前進而 `git apply` 失敗，改用 `git apply --3way`。只動 `Beta.lean` 尾端與開頭說明的一行，衝突機會很小。
- 檔頭 `Authors:` 是原作者 David Loeffler；小幅增補通常不改，要不要加上你的名字由你決定。
- 審稿人可能要求：改名（例如把 `_of_re_pos` 換成別的慣用後綴）、把兩個輔助引理併進主證明、或改放到別的檔。這些都是正常來回；改完重跑上面兩行檢查即可。
- 節點上的驗證環境保留在 `~/alloy_node/upstream/gamma_check/`（約 7.8 GB），方便日後照審稿意見修改後重編；不需要時可以刪。
