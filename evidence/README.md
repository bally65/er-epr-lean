# evidence（公開版）

- `*_lakebuild/`：每次乾淨重建（`lake build --wfail`）收回的收據 `receipt.txt`（主機、版本、每個原始碼檔的 sha256、逐步 rc）、公理清單 `axioms.out`、耦合斷言結果 `coupling.out`。
- `drills_*/REPORT.md`：反向演習全量重跑的報告（每份演習改壞了什麼、哪些宣告變紅、反例區塊是否成立）。

完整紀錄（探針、逐份演習的編譯輸出、原始碼快照）留在作者的私人 repo。要自己驗證，直接在根目錄 `lake exe cache get && lake build`。
