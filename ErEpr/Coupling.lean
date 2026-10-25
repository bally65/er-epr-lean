import ErEpr.Chain
import ErEpr.KMSPair
import ErEpr.MinCut
import ErEpr.Charts
import ErEpr.Klein
import ErEpr.Triangle
import ErEpr.Modular
import ErEpr.FirstLaw
import ErEpr.FirstLawGeneral
import ErEpr.Unruh
import ErEpr.Landauer
import ErEpr.Correlated
import ErEpr.Measurement
import ErEpr.Monogamy
import ErEpr.Swapping

/-!
# ErEpr.Coupling：耦合檢驗（機械化）

對每條「接兩側」或「接兩站」的定理，遞迴展開它在 `ErEpr` 命名空間內用到的常數
（型別與證明體都展開；mathlib 的常數不展開），檢查指定的錨點確實在依賴閉包裡。
另有反向檢查：某些定理**不得**依賴某些錨點（例如不可能定理只靠 EPR 側，不依賴 ER 側）。
任何一條不符就 `logError`，在 `-DwarningAsError=true` 下編譯失敗。

這取代先前「只看原始碼判斷有沒有用到」的做法（見 `EVIDENCE.md` B0＋B1 一節的限定）。
-/

open Lean Elab Command

namespace ErEpr.Coupling

/-- 常數 `n` 在本庫（`ErEpr.*`）內的依賴閉包，含 `n` 自己。 -/
def closure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [n]
  for _ in [0:1000000] do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      unless seen.contains c do
        seen := seen.insert c
        if let some ci := env.find? c then
          -- 定理的證明體要明寫取出：`ConstantInfo.value?` 預設不給 opaque，
          -- 且取不到時會靜默回 `none`，閉包就不展開（獨立性檢驗會假綠燈）。
          let v : Option Expr := match ci with
            | .thmInfo t => some t.value
            | .defnInfo d => some d.value
            | .opaqueInfo o => some o.value
            | _ => none
          let deps := ci.type.getUsedConstants ++ (v.map Expr.getUsedConstants).getD #[]
          for d in deps do
            if (`ErEpr).isPrefixOf d then
              todo := d :: todo
  return seen

/-- `#assert_uses t => a₁ a₂ …`：`t` 的依賴閉包必須含每個 `aᵢ`。 -/
elab "#assert_uses " t:ident " => " as:ident* : command => do
  let env ← getEnv
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let cl := closure env tn
  let mut ok := true
  for a in as do
    let an ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
    unless cl.contains an do
      logError m!"耦合檢驗失敗：{tn} 沒有用到 {an}（閉包 {cl.size} 個本庫常數）"
      ok := false
  if ok then
    logInfo m!"耦合通過：{tn} 用到 {as.map (·.getId)}（閉包 {cl.size} 個本庫常數）"

/-- `#assert_not_uses t => a₁ a₂ …`：`t` 的依賴閉包不得含任何 `aᵢ`。 -/
elab "#assert_not_uses " t:ident " => " as:ident* : command => do
  let env ← getEnv
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let cl := closure env tn
  let mut ok := true
  -- 閉包裡除了自己之外沒有任何定理 ⇒ 證明體多半沒有展開（只展開了型別），
  -- 「不依賴」是空洞的，直接判紅。
  let thms := cl.toList.filter fun c => c != tn && (env.find? c matches some (.thmInfo _))
  if thms.isEmpty then
    logError m!"獨立性檢驗不可信：{tn} 的閉包（{cl.size} 個常數）裡沒有其他定理，證明體可能沒展開"
    ok := false
  for a in as do
    let an ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
    if cl.contains an then
      logError m!"獨立性檢驗失敗：{tn} 用到了 {an}"
      ok := false
  if ok then
    logInfo m!"獨立通過：{tn} 不依賴 {as.map (·.getId)}（閉包 {cl.size} 個本庫常數）"

end ErEpr.Coupling

namespace ErEpr

/-! ## 跨欄耦合：ER 側錨點確實進了 EPR 側定理 -/

#assert_uses no_gibbs_matches_first_law =>
  hawking_beta first_law_area no_finite_dim_gibbs_matches_bh_mass antitoneOn_gibbsEntropyFn
#assert_uses no_gibbs_matches_unitConeAngle => hawking_beta no_finite_dim_gibbs_matches_bh_mass
#assert_uses first_law_area => hawking_beta conicalRatio_tendsto

/-! ## 獨立性：不可能定理只靠 EPR 側 -/

#assert_not_uses no_finite_dim_gibbs_matches_bh => hawking_beta first_law_area conicalRatio
#assert_not_uses antitoneOn_gibbsEntropyFn => hawking_beta first_law_area

/-! ## 站與站之間 -/

#assert_uses ptrB_idKron_tfdState => ptrB_idKron ptrB_tfdState
#assert_uses ptrB_tfdState => tfdAmp_mul_conjTranspose exp_neg_smul_eigen
#assert_uses tfd_ptrA_isKMS => ptrA_tfdState gibbs_isKMS
#assert_uses gibbs_tracial_iff_scalar => KMSPair.tracial_iff_period gibbs_isKMS
#assert_uses Kraus.no_signalling => ptrB_idKron idKron_unique
#assert_uses vnEntropy_cut_mpsOpen_le => rank_cutAt_mpsOpen_le vnEntropy_le_log_rank chainProd_append
#assert_uses rank_cutMat_tnAmp_le => cutMat_tnAmp
-- 推論 `ghz4_not_minCut` 與 `ghz4_mmi_fails` 是兩條平行的證明，共用 `regionEntropy_ghz`；
-- 推論並不是接在 `ghz4_mmi_fails` 上（2026-10-24 機械檢驗發現，原先的說法是看原始碼猜的）。
#assert_uses ghz4_not_minCut => minCut_mmi regionEntropy_ghz mmi_contract
#assert_uses ghz4_mmi_fails => regionEntropy_ghz
#assert_not_uses ghz4_not_minCut => ghz4_mmi_fails
#assert_uses inversion_swaps_UV => sliceX_inv
#assert_uses gibbs_dS_eq_beta_dE => hasDerivAt_gibbsEntropyFn hasDerivAt_energyMean

/-! ## Klein（S5 後半）：不等式只靠固有分解與逐項不等式；等號方向才用到 Gibbs 閉式 -/

#assert_uses vnEntropy_le_beta_energy_add_log =>
  klein_gap_eq kleinGap_nonneg vnEntropy_eq_sum_eigenvalues trace_mul_eq_sum
#assert_uses vnEntropy_eq_beta_energy_add_log_iff =>
  gibbs_eq_conj vnEntropy_gibbs_eq_fn trace_gibbs_mul_self kleinGap_pos
#assert_not_uses vnEntropy_le_beta_energy_add_log => vnEntropy_gibbs_eq_fn hawking_beta first_law_area
#assert_uses negctrl_klein_pure_H2 => vnEntropy_eq_beta_energy_add_log_iff gibbs_H2_log2

/-! ## 三角（docs/TRIANGLE.md）：T-b 只靠 Klein；T-a、T-e 只靠 ER 側，不經 Klein -/

#assert_uses reservoir_entropy_le_beta_heat =>
  vnEntropy_le_beta_energy_add_log vnEntropy_gibbs_eq_beta_energy_add_log
#assert_not_uses reservoir_entropy_le_beta_heat => hawking_beta first_law_area
#assert_uses first_law_saturates_bekenstein => first_law_area rOfRho_throat throat_area_eq
#assert_not_uses first_law_saturates_bekenstein => vnEntropy_le_beta_energy_add_log klein_gap_eq
#assert_uses bh_landauer_saturated => hawking_beta hasDerivAt_bh_energy_of_entropy
#assert_not_uses bh_landauer_saturated => vnEntropy_le_beta_energy_add_log klein_gap_eq

/-! ## T-c（模哈密頓量與相對熵）：沿用 T-b 與 Klein，不碰 ER 側 -/

#assert_uses entropy_le_modular =>
  reservoir_entropy_le_beta_heat gibbs_modHamOf exp_neg_modHamOf
#assert_uses relEntropyOf_nonneg => vnEntropy_le_beta_energy_add_log partZ_modHamOf
#assert_not_uses entropy_le_modular => hawking_beta first_law_area
#assert_uses modHamOf_gibbs => eigU_spectral

/-! ## 糾纏第一定律：兩條路互不依賴 -/

#assert_uses entanglement_first_law_diag => hasDerivAt_entropy_diagPath hasDerivAt_modEnergy_diagPath
#assert_not_uses entanglement_first_law_diag => relEntropyOf_nonneg vnEntropy_le_beta_energy_add_log
#assert_uses first_law_of_relEntropy_min => relEntropyOf_nonneg relEntropyOf_diagonal
#assert_not_uses first_law_of_relEntropy_min =>
  hasDerivAt_entropy_diagPath hasDerivAt_modEnergy_diagPath entanglement_first_law_diag
#assert_uses relEntropy_diagPath_pos => relEntropyOf_eq_zero_iff

/-! ## 不對易第一定律：夾擠與極小值兩條路互不依賴，也不依賴對易版 -/

#assert_uses hasDerivAt_entropy_gibbsPath =>
  klein_gap_le_sq vnEntropy_le_beta_energy_add_log eventually_gibbsPath_posSemidef
#assert_not_uses hasDerivAt_entropy_gibbsPath =>
  hasDerivAt_entropy_diagPath first_law_gibbs_of_hasDerivAt
#assert_not_uses first_law_gibbs_of_hasDerivAt => klein_gap_le_sq hasDerivAt_entropy_gibbsPath
#assert_uses entanglement_first_law => hasDerivAt_entropy_gibbsPath gibbs_modHamOf
#assert_not_uses entanglement_first_law => hawking_beta first_law_area
#assert_uses first_law_general_agrees_diag => entanglement_first_law hasDerivAt_entropy_diagPath

/-! ## X₁′（Unruh 核心）：熱分佈獨立定義；表面重力那條路不經錐角 -/

#assert_uses integral_gammaKernel => differentiableAt_gammaIntegral integrableOn_gammaKernel
#assert_uses bogoliubov_ratio_sq_tendsto =>
  bogoliubov_ratio_tendsto bogoliubov_ratio_regularized integral_gammaKernel
#assert_not_uses bogoliubov_ratio_regularized => hawking_beta first_law_area
#assert_not_uses meanOccupation_eq => integral_gammaKernel bogoliubov_ratio_regularized
#assert_not_uses hasDerivAt_FS_horizon => hawking_beta conicalRatio_tendsto
#assert_uses unitConeAngle_of_surfaceGravity => hawking_beta surfaceGravity_schwarzschild

/-! ## T-d（完整 Landauer）：四塊各自到位；次可加性不經 T-b；可加性不經 Klein -/

#assert_uses landauer =>
  vnEntropy_subadditive vnEntropy_kronecker vnEntropy_unitary_conj reservoir_entropy_le_beta_heat
#assert_uses vnEntropy_subadditive =>
  relEntropyOf_nonneg modHamOf_kronecker trace_ptrA_mul trace_ptrB_mul tendsto_mul_log_mixUnif
#assert_not_uses vnEntropy_subadditive => reservoir_entropy_le_beta_heat entropy_le_modular
#assert_not_uses vnEntropy_kronecker => vnEntropy_le_beta_energy_add_log klein_gap_eq
#assert_not_uses landauer => hawking_beta first_law_area
#assert_uses landauer_swap_witness => swapU_conj_kronecker vnEntropy_gibbs_H2_log2_lt
#assert_uses negctrl_landauer_not_unitary => resetS_conj_mix2 ptrA_kronecker

/-! ## 糾纏起點：同一個解糾纏矩陣；負控制不偷用 Landauer；古典對照不經 Bell -/

#assert_uses vnEntropy_bell => disentangle_conj_maxEnt vnEntropy_kronecker vnEntropy_unitary_conj
#assert_not_uses vnEntropy_bell => vnEntropy_le_log_rank
#assert_uses negctrl_landauer_correlated => disentangle_conj_maxEnt ptrA_bell_eq_gibbs
#assert_not_uses negctrl_landauer_correlated => landauer vnEntropy_subadditive
#assert_uses correlation_is_fuel => product_start_no_erasure landauer disentangle_conj_maxEnt
#assert_not_uses vnEntropy_ptrB_diagonal_le => vnEntropy_subadditive disentangle_conj_maxEnt

/-! ## 觀測：只動系統、只動儀器兩條「解不開」互不依賴；整體熵的兩個 0 由獨立的路算出 -/

#assert_uses local_cannot_undo => ptrB_local_conj vnEntropy_unitary_conj cnot_measure
#assert_not_uses local_cannot_undo => Kraus.no_signalling
#assert_uses pointer_cannot_undo => Kraus.no_signalling cnot_measure
#assert_not_uses pointer_cannot_undo => ptrB_local_conj
#assert_uses measurement_entropy => vnEntropy_bell vnEntropy_plusProj vnEntropy_kronecker
#assert_not_uses vnEntropy_plusProj => vnEntropy_bell disentangle_conj_maxEnt
#assert_uses joint_undo => disentangle_conj_maxEnt cnot_mul_self

/-! ## 一夫一妻：半正定那一步不經 Klein 與相對熵；I(A:C)=0 由張量積可加；負控制不經主定理 -/

#assert_uses monogamy => mul_eq_zero_of_trace_mul_eq_zero rankOne_kron_one_conj trace_ptrB_mul
#assert_not_uses monogamy => vnEntropy_le_beta_energy_add_log relEntropyOf_nonneg
#assert_uses monogamy_mutualInfo => monogamy ptrMid_kronecker vnEntropy_kronecker
#assert_uses bell_monogamy => monogamy_mutualInfo bell_mutual_information
#assert_not_uses negctrl_monogamy_mixed => monogamy mul_eq_zero_of_trace_mul_eq_zero

/-! ## 糾纏交換：交換用 Bell 投影；平均那條不經交換定理；負控制不經 Bell 投影 -/

#assert_uses entanglement_swapping => swapProj_mulVec ptrBC_swap_post bell_mutual_information
#assert_uses swap_average_no_signalling => swap_average_eq ptrBC_kronecker
#assert_not_uses swap_average_no_signalling => entanglement_swapping
#assert_uses negctrl_swap_separate => sepProj_mulVec mutualInfo_kronecker
#assert_not_uses negctrl_swap_separate => swapProj swapProj_mulVec

/-! ## 洞的形狀：AMPS 矛盾用一夫一妻；負控制不經主定理；不可能定理的負控制不經單調性 -/

#assert_uses amps_contradiction => amps_monogamy monogamy ptrFirst_kronecker
#assert_uses amps_each_half_satisfiable => bell_monogamy_witness ptrFirst_ampsUnitaryState
#assert_not_uses negctrl_amps_mixed => monogamy amps_monogamy
#assert_uses negctrl_nogo_varying_hamiltonian =>
  exists_hamiltonian_gibbs_entropy_eq gibbs_diagonal_real vnEntropy_diagonal
#assert_not_uses negctrl_nogo_varying_hamiltonian =>
  antitoneOn_gibbsEntropyFn no_finite_dim_gibbs_matches_bh hasDerivAt_gibbsEntropyFn
#assert_uses nogo_hinges_on_fixed_hamiltonian =>
  no_finite_dim_gibbs_matches_bh negctrl_nogo_varying_hamiltonian

/-! ## 面積律：上界走秩；等號見證與負控制是直接算的，不經上界 -/

#assert_uses cutEntropy_tnAmp_le => rank_cutMat_tnAmp_le vnEntropy_le_log_rank
#assert_not_uses area_law_saturated => cutEntropy_tnAmp_le rank_cutMat_tnAmp_le
#assert_not_uses negctrl_nonlocal_entropy => cutEntropy_tnAmp_le rank_cutMat_tnAmp_le

/-! ## Π 是投影：走重排與秩一投影，不經逐格計算的核心一行 -/

#assert_uses swapProj_mul_self => swapProj_eq_reindex rankOne_mul_self
#assert_not_uses swapProj_mul_self => swapProj_mulVec entanglement_swapping
#assert_uses sum_swapProj => swapProj_eq_reindex sum_bellProjBC

/-! ## T1 很薄：主定理不需要 idKron 的唯一性（唯一性只保證定義是對的） -/

#assert_not_uses ptrB_idKron => idKron_unique

end ErEpr
