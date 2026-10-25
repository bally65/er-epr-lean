import ErEpr.NoSignalling
import ErEpr.TFD
import ErEpr.MPS
import ErEpr.Entropy
import ErEpr.ER
import ErEpr.Hawking
import ErEpr.TensorNetwork
import ErEpr.NoGo
import ErEpr.Chain
import ErEpr.KMS
import ErEpr.KMSPair
import ErEpr.Charts
import ErEpr.MinCut
import ErEpr.Coupling

/-! 公理檢查：每條都必須只出現 `[propext, Classical.choice, Quot.sound]`。 -/

open ErEpr

-- Basic：保真引理 F1–F8 與純態約化
#print axioms trace_ptrB_mul
#print axioms ptrB_kronecker
#print axioms trace_ptrB
#print axioms ptrB_posSemidef
#print axioms ptrB_pure
#print axioms ptrA_pure
#print axioms ptrB_maxEnt
#print axioms ptrA_maxEnt
#print axioms ptrB_ne_ptrA_witness
#print axioms idKron_kronecker
#print axioms idKron_unique
-- T1 與 Kraus 推論
#print axioms ptrB_idKron
#print axioms trace_sandwich
#print axioms sandwich_one_kron
#print axioms Kraus.trace_toLin
#print axioms Kraus.app_eq_idKron
#print axioms Kraus.no_signalling
-- 負控制
#print axioms negctrl_not_tp
#print axioms kUnital_unital
#print axioms kUnital_not_tp
#print axioms negctrl_unital_not_tp
#print axioms negctrl_replace_changes_ptrA
#print axioms negctrl_A_side_changes_ptrB
-- 見證
#print axioms ampK_not_unital
#print axioms witness_pauliX
#print axioms witness_amplitudeDamping
#print axioms witness_transpose
-- T2 熱場雙態
#print axioms gibbs_diagonal_real
#print axioms trace_pureOf
#print axioms exp_neg_smul_eigen
#print axioms trace_exp_neg_smul_ne_zero
#print axioms tfdAmp_mul_conjTranspose
#print axioms ptrB_tfdState
#print axioms ptrA_tfdState
#print axioms trace_tfdState
#print axioms exp_neg_smul_pauliY
#print axioms gibbs_pauliY_ne_transpose
#print axioms negctrl_ptrA_ne_gibbs
#print axioms gibbs_H2_log2
#print axioms negctrl_sign_flip
#print axioms negctrl_missing_half
-- T3 MPS 秩上界
#print axioms chainProd_append
#print axioms rank_cutAt_mpsOpen_le
#print axioms rank_cutAt_mpsRing_le
#print axioms rank_ptrB_pure
#print axioms rank_ptrB_mpsOpen_le
#print axioms cutAt_bell
#print axioms rank_cutAt_bell
-- 第二批：von Neumann 熵
#print axioms vnEntropy_eq_sum_eigenvalues
#print axioms vnEntropy_diagonal
#print axioms vnEntropy_maxMixed
#print axioms vnEntropy_ptrB_maxEnt
#print axioms vnEntropy_le_log_rank
#print axioms vnEntropy_le_log_of_rank_le
#print axioms vnEntropy_mul_comm
#print axioms vnEntropy_ptrA_pureOf_eq
#print axioms vnEntropy_ptrA_tfdState
#print axioms vnEntropy_cut_mpsOpen_le
#print axioms vnEntropy_cut_mpsRing_le
#print axioms trace_bellN
#print axioms vnEntropy_cut_bellN
#print axioms negctrl_unnormalized
-- ER 側
#print axioms FutureCausal.nonneg
#print axioms kruskal_monotone
#print axioms no_causal_curve_between_exteriors
#print axioms meet_in_interior
#print axioms bridge_slice_spacelike
#print axioms negctrl_spacelike_connects
#print axioms throat_area_le
#print axioms throat_area_eq
#print axioms hasDerivAt_inversion
#print axioms inversion_isometry
#print axioms inversion_fixed
-- ER-3 與收尾
#print axioms properDist_hasDerivAt
#print axioms properDist_r_hasDerivAt
#print axioms conicalRatio_tendsto
#print axioms hawking_beta
#print axioms negctrl_wrong_beta
#print axioms first_law_area
#print axioms first_law_witness
-- 補缺口：T2d、u⊗ū、錯振幅負控制
#print axioms vecOf_tfdAmp
#print axioms tfd_boost_invariant
#print axioms ptrB_pureOf_wrong
#print axioms ptrA_pureOf_wrong
#print axioms negctrl_wrong_amplitude
#print axioms rank_cutAt_ringBell
#print axioms transposeMap_not_completelyPositive
-- 環狀熵緊度
#print axioms cutAt_mpsRing_smul
#print axioms cutAt_ringBellN
#print axioms trace_ringBellN
#print axioms vnEntropy_cut_ringBellN
-- 一般圖張量網路的 ∀ 割秩上界
#print axioms inW_of_inc_mem
#print axioms not_inW_of_inc_nmem
#print axioms cutMat_tnAmp
#print axioms rank_cutMat_tnAmp_le
#print axioms tnAmp_path2TN
#print axioms tnAmp_bellTN
#print axioms card_cutEdges_path2
#print axioms rank_cutMat_bellTN
#print axioms tnAmp_ring2TN
#print axioms tnAmp_ringBellTN
#print axioms card_cutEdges_ring2
#print axioms rank_cutMat_ringBellTN
#print axioms card_cutEdges_loop
#print axioms rank_cutMat_loop_le
#print axioms tnAmpAll_loopT
#print axioms negctrl_nonlocal_tensor
-- B0 修正：ER-3 單位錐角條件、T2d 與 β 無關、積分常數負控制
#print axioms conicalRatio_eq_coneAngleRatio
#print axioms coneAngleRatio_cone
#print axioms coneAngleRatio_cone_not_unit
#print axioms negctrl_first_law_const
#print axioms boost_mulVec_vecOf
#print axioms boost_invariant_iff_commute
#print axioms boost_invariant_one
#print axioms tfdAmp_zero
#print axioms tfd_boost_invariant_zero
-- B0 修正：T1∘T2 組合
#print axioms ptrB_idKron_tfdState
-- B1 不可能定理
#print axioms partZ_nonneg
#print axioms partZ_pos
#print axioms trace_exp_neg_smul_eq
#print axioms gibbs_eq_conj
#print axioms vnEntropy_unitary_conj
#print axioms vnEntropy_gibbs
#print axioms vnEntropy_gibbs_eq_fn
#print axioms vnEntropy_gibbs_nonneg
#print axioms hasDerivAt_bw
#print axioms hasDerivAt_partZ
#print axioms hasDerivAt_partN
#print axioms hasDerivAt_gibbsEntropyFn
#print axioms sq_sum_le_mul_sum
#print axioms energyVar_nonneg
#print axioms antitoneOn_gibbsEntropyFn
#print axioms no_gibbs_entropy_strictMonoOn
#print axioms no_finite_dim_gibbs_matches_bh
#print axioms no_finite_dim_gibbs_matches_bh_mass
#print axioms gibbs_zero
#print axioms vnEntropy_gibbs_zero
#print axioms gibbsEntropyFn_zero
#print axioms vnEntropy_gibbs_le_log_card
#print axioms gibbs_posSemidef
#print axioms trace_gibbs
#print axioms vnEntropy_gibbs_le_log_card_of_rank
#print axioms negctrl_single_point
#print axioms negctrl_single_point_H2
-- 耦合版不可能定理（接 ER 側錨點）
#print axioms no_gibbs_matches_unitConeAngle
#print axioms no_gibbs_matches_first_law
-- B2 KMS 線：S1 歐氏準備
#print axioms tfdAmp_eq_exp
#print axioms exp_half_mul_conjTranspose
#print axioms tfdAmp_mul_conjTranspose'
#print axioms tfdAmp_isUnit
#print axioms negctrl_tfdAmp_full_beta
-- B2 KMS 線：S3 純化唯一
#print axioms vecOf_mul
#print axioms purification_unique_of_isUnit
#print axioms tfd_purification_unique
#print axioms tfdAmpWrong_eq
#print axioms eigU_mul_transpose_unitary
#print axioms vecOf_tfdAmpWrong
-- B2 KMS 線：S2 KMS 逆向唯一
#print axioms exp_neg_mul_exp
#print axioms exp_mul_exp_neg
#print axioms exp_smul_diagonal
#print axioms conj_mul_conj
#print axioms nuStep_mul
#print axioms nuStep_one
#print axioms nuStepAlgHom_apply
#print axioms conj_eq_self_iff
#print axioms trace_conj_cycle
#print axioms gibbs_isKMS
#print axioms kms_core
#print axioms isKMS_unique
#print axioms isKMS_iff_eq_gibbs
#print axioms gibbs_transpose
#print axioms tfd_ptrB_isKMS
#print axioms tfd_ptrA_isKMS
#print axioms diagonal_mul_single_mul_diagonal
#print axioms negctrl_scalar_not_kms
#print axioms negctrl_maxMixed_not_kms
-- B2 KMS 線：S4 KMSPair 與 tracial ⇔ 週期
#print axioms KMSPair.tracial_iff_period
#print axioms KMSPair.ofComm
#print axioms gibbs_mul_inv
#print axioms gibbs_isUnit
#print axioms gibbsKMSPair_ω
#print axioms gibbsKMSPair_ν
#print axioms gibbs_tracial_iff_scalar
#print axioms negctrl_diag_not_tracial
#print axioms negctrl_gibbs_not_tracial
#print axioms negctrl_nondeg_needed
#print axioms no_ringHom_matrix_to_comm
-- B3 ER 側接縫（Charts）：K1 三張圖、K1′ 反演 = U ↔ V、K2 boost、K4 鞍點
#print axioms hasDerivAt_kf
#print axioms kf_strictMonoOn
#print axioms kf_two_M
#print axioms kf_pos_iff
#print axioms kf_neg_iff
#print axioms kf_eq_zero_iff
#print axioms FS_pos
#print axioms FK_mul_kf
#print axioms hasDerivAt_sqrt_kf
#print axioms FK_mul_dsqrtkf_sq
#print axioms FK_mul_deriv_sqrt_kf
#print axioms kruskalU_mul_V
#print axioms kruskalV_div_U
#print axioms kruskal_rightExterior
#print axioms kruskal_pullback
#print axioms rOfRho_eq
#print axioms rOfRho_pos
#print axioms rOfRho_throat
#print axioms FS_rOfRho
#print axioms hasDerivAt_rOfRho
#print axioms confIso_eq_rOfRho
#print axioms areaIso_eq_rOfRho
#print axioms iso_radial
#print axioms iso_angular
#print axioms rOfRho_inv
#print axioms sliceX_inv
#print axioms sliceX_sq
#print axioms sliceX_deriv_alg
#print axioms hasDerivAt_sliceX
#print axioms FK_mul_deriv_sliceX_sq
#print axioms sliceX_throat
#print axioms slice_rightExterior
#print axioms slice_leftExterior
#print axioms slice_prod
#print axioms inversion_swaps_UV
#print axioms boost_preserves_prod
#print axioms boost_metric
#print axioms exp_mul_pos_iff
#print axioms exp_mul_neg_iff
#print axioms futureCausal_boost_of
#print axioms futureCausal_boost
#print axioms rightExterior_boost
#print axioms leftExterior_boost
#print axioms futureInterior_boost
#print axioms negctrl_boost_spacelike
#print axioms r_gt_of_slice
#print axioms r_lt_of_timelike
#print axioms r_eq_at_bifurcation
#print axioms area_lt_area_iff
#print axioms area_slice_gt
#print axioms area_timelike_lt
#print axioms area_bifurcation_eq
#print axioms negctrl_interior_area
-- B4 圖對態的約束（MinCut）：G6 次模性、G5 MMI、GHZ 違反、G1、G2
#print axioms card_cutEdges_eq_sum
#print axioms cutInd_submod
#print axioms cutEdges_card_submodular
#print axioms cutEdges_compl
#print axioms minCut_le
#print axioms exists_minCut
#print axioms mmi_contract
#print axioms mmi_boundary
#print axioms decide_mem_contractSet
#print axioms contractSet_inter
#print axioms decide_mem_of_inter
#print axioms decide_and_eq_false_of_disjoint
#print axioms minCut_mmi
#print axioms regionState_eq_ptrB_reindex
#print axioms vnEntropy_reindex
#print axioms merge_eq_const
#print axioms cutMat_ghz
#print axioms sBell_mul_star
#print axioms two_point_entry
#print axioms regionState_ghz
#print axioms negMulLog_sum_two
#print axioms regionEntropy_ghz
#print axioms trace_regionState_ghz
#print axioms ghz4_mmi_fails
#print axioms ghz4_not_minCut
#print axioms rank_le_one_iff_vecMulVec
#print axioms tnAmp_product_of_no_cut
#print axioms tnAmp_rankOne
#print axioms rank_cutMat_rankOne_le
#print axioms negctrl_product_with_bond
#print axioms rank_cutMat_eq_of_inj_surj
-- S5 便宜半段
#print axioms trace_gibbs_mul_self
#print axioms hasDerivAt_energyMean
#print axioms gibbs_dS_eq_beta_dE
#print axioms gibbs_entropy_energy_slope


-- S5 的 Klein 那一半（ErEpr/Klein.lean）
#print axioms ErEpr.kleinGap_nonneg
#print axioms ErEpr.kleinGap_pos
#print axioms ErEpr.klein_sum_identity
#print axioms ErEpr.klein_real
#print axioms ErEpr.nonempty_of_trace_eq_one
#print axioms ErEpr.sum_normSq_row
#print axioms ErEpr.sum_normSq_col
#print axioms ErEpr.trace_diag_mul_diag
#print axioms ErEpr.eigU_cross_mul_star
#print axioms ErEpr.eigU_cross_star_mul
#print axioms ErEpr.trace_mul_eq_sum
#print axioms ErEpr.sum_eigenvalues_of_trace_eq_one
#print axioms ErEpr.klein_gap_eq
#print axioms ErEpr.vnEntropy_le_beta_energy_add_log
#print axioms ErEpr.vnEntropy_eq_beta_energy_add_log_iff
#print axioms ErEpr.vnEntropy_gibbs_eq_beta_energy_add_log
#print axioms ErEpr.vnEntropy_le_gibbs_of_energy_eq
#print axioms ErEpr.vnEntropy_lt_gibbs_of_energy_eq
#print axioms ErEpr.ket0Proj_posSemidef
#print axioms ErEpr.trace_ket0Proj
#print axioms ErEpr.negctrl_klein_pure_H2
#print axioms ErEpr.negctrl_klein_other_beta_H2


-- 物質－能量－信息三角的便宜磚（ErEpr/Triangle.lean）
#print axioms ErEpr.bekensteinBound_throat
#print axioms ErEpr.first_law_saturates_bekenstein
#print axioms ErEpr.negctrl_bekenstein_isotropic_radius
#print axioms ErEpr.reservoir_entropy_le_beta_heat
#print axioms ErEpr.reservoir_entropy_eq_beta_heat_iff
#print axioms ErEpr.landauer_reservoir_bit
#print axioms ErEpr.negctrl_reservoir_not_gibbs
#print axioms ErEpr.bh_energy_of_entropy
#print axioms ErEpr.hasDerivAt_bh_energy_of_entropy
#print axioms ErEpr.bh_landauer_saturated


-- T-c 模哈密頓量與相對熵（ErEpr/Modular.lean）
#print axioms ErEpr.modHamOf_isHermitian
#print axioms ErEpr.exp_neg_modHamOf
#print axioms ErEpr.trace_unitary_conj_diag
#print axioms ErEpr.gibbs_modHamOf
#print axioms ErEpr.partZ_modHamOf
#print axioms ErEpr.modHamOf_gibbs
#print axioms ErEpr.entropy_le_modular
#print axioms ErEpr.entropy_eq_modular_iff
#print axioms ErEpr.relEntropyOf_nonneg
#print axioms ErEpr.relEntropyOf_eq_zero_iff
#print axioms ErEpr.relEntropyOf_diagonal
#print axioms ErEpr.entropy_le_modHam
#print axioms ErEpr.negctrl_modular_not_fullRank


-- 糾纏第一定律（ErEpr/FirstLaw.lean）
#print axioms ErEpr.vnEntropy_diagPath
#print axioms ErEpr.modEnergy_diagPath
#print axioms ErEpr.trace_diagPath
#print axioms ErEpr.diagPath_posSemidef
#print axioms ErEpr.hasDerivAt_entropy_diagPath
#print axioms ErEpr.hasDerivAt_modEnergy_diagPath
#print axioms ErEpr.entanglement_first_law_diag
#print axioms ErEpr.eventually_diagPath_pos
#print axioms ErEpr.first_law_of_relEntropy_min
#print axioms ErEpr.relEntropy_diagPath_pos
#print axioms ErEpr.negctrl_first_law_wrong_reference


-- 不對易的糾纏第一定律（ErEpr/FirstLawGeneral.lean）
#print axioms ErEpr.kleinGap_le_sq
#print axioms ErEpr.sum_sq_doubly_stochastic
#print axioms ErEpr.trace_mul_self_eq_sum
#print axioms ErEpr.trace_gibbs_mul_self_eq_sum
#print axioms ErEpr.trace_mul_gibbs_eq_sum
#print axioms ErEpr.trace_sub_gibbs_sq_eq_sum
#print axioms ErEpr.klein_gap_le_sq
#print axioms ErEpr.exists_gibbs_lower
#print axioms ErEpr.trace_gibbsPath
#print axioms ErEpr.gibbsPath_zero
#print axioms ErEpr.energy_gibbsPath
#print axioms ErEpr.sq_gibbsPath
#print axioms ErEpr.gibbs_sub_smul_one_posSemidef
#print axioms ErEpr.eventually_smul_one_add_posSemidef
#print axioms ErEpr.eventually_gibbsPath_posSemidef
#print axioms ErEpr.hasDerivAt_entropy_gibbsPath
#print axioms ErEpr.first_law_gibbs_of_hasDerivAt
#print axioms ErEpr.entanglement_first_law
#print axioms ErEpr.first_law_general_agrees_diag
#print axioms ErEpr.negctrl_first_law_not_fullRank


-- X₁′ 類比重力核心（ErEpr/GammaRotation.lean、ErEpr/Unruh.lean）
#print axioms ErEpr.norm_gammaKernel
#print axioms ErEpr.continuousOn_gammaKernel
#print axioms ErEpr.integrableOn_gammaKernel
#print axioms ErEpr.hasDerivAt_gammaKernel
#print axioms ErEpr.differentiableAt_gammaIntegral
#print axioms ErEpr.integral_gammaKernel
#print axioms ErEpr.meanOccupation_eq
#print axioms ErEpr.bogoliubov_thermal
#print axioms ErEpr.negctrl_bogoliubov_fermi
#print axioms ErEpr.hasDerivAt_FS_horizon
#print axioms ErEpr.surfaceGravity_schwarzschild
#print axioms ErEpr.unitConeAngle_of_surfaceGravity
#print axioms ErEpr.bogoliubov_ratio_regularized
#print axioms ErEpr.bogoliubov_ratio_tendsto
#print axioms ErEpr.bogoliubov_ratio_sq_tendsto
#print axioms ErEpr.bogoliubov_factor_schwarzschild
#print axioms ErEpr.negctrl_no_horizon

-- T-d 完整 Landauer（ErEpr/Landauer.lean）
#print axioms ErEpr.trace_ptrA_mul
#print axioms ErEpr.ptrA_kronecker
#print axioms ErEpr.trace_ptrA
#print axioms ErEpr.ptrA_posSemidef
#print axioms ErEpr.star_kronecker
#print axioms ErEpr.kronecker_star_mul
#print axioms ErEpr.kronecker_mul_star
#print axioms ErEpr.coe_kronU
#print axioms ErEpr.kronecker_spectral
#print axioms ErEpr.vnEntropy_kronecker
#print axioms ErEpr.modHamOf_kronecker
#print axioms ErEpr.trace_mul_modHamOf_of_eq
#print axioms ErEpr.vnEntropy_le_marginal_cross
#print axioms ErEpr.mixUnif_pos
#print axioms ErEpr.sum_mixUnif
#print axioms ErEpr.tendsto_mul_log_mixUnif
#print axioms ErEpr.vnEntropy_le_of_marginal_spectral
#print axioms ErEpr.vnEntropy_subadditive
#print axioms ErEpr.landauer
#print axioms ErEpr.landauer_bit
#print axioms ErEpr.no_heatless_erasure
#print axioms ErEpr.swapU_mul_apply
#print axioms ErEpr.mul_swapU_apply
#print axioms ErEpr.star_swapU
#print axioms ErEpr.swapU_star_mul
#print axioms ErEpr.swapU_conj_kronecker
#print axioms ErEpr.mix2_posSemidef
#print axioms ErEpr.trace_mix2
#print axioms ErEpr.vnEntropy_mix2
#print axioms ErEpr.vnEntropy_ket0Proj
#print axioms ErEpr.vnEntropy_gibbs_H2_log2_lt
#print axioms ErEpr.landauer_swap_witness
#print axioms ErEpr.resetS_not_unitary
#print axioms ErEpr.resetS_conj_mix2
#print axioms ErEpr.negctrl_landauer_not_unitary
#print axioms ErEpr.negctrl_subadditive_unnormalized

-- 糾纏起點（ErEpr/Correlated.lean）
#print axioms ErEpr.star_bellK
#print axioms ErEpr.bellK_mul_self
#print axioms ErEpr.bellK_conj_maxEnt
#print axioms ErEpr.sBell_mul_self_complex
#print axioms ErEpr.star_disentangle
#print axioms ErEpr.disentangle_mul_self
#print axioms ErEpr.disentangle_star_mul
#print axioms ErEpr.disentangle_conj_maxEnt
#print axioms ErEpr.maxEnt_eq_disentangle_conj
#print axioms ErEpr.vnEntropy_bell
#print axioms ErEpr.vnEntropy_ptrB_bell
#print axioms ErEpr.vnEntropy_ptrA_bell
#print axioms ErEpr.bell_conditional_entropy
#print axioms ErEpr.bell_mutual_information
#print axioms ErEpr.negctrl_entropy_monotone
#print axioms ErEpr.negMulLog_sum_le
#print axioms ErEpr.vnEntropy_ptrB_diagonal_le
#print axioms ErEpr.gibbs_zero_ham
#print axioms ErEpr.product_start_no_erasure
#print axioms ErEpr.ptrA_bell_eq_gibbs
#print axioms ErEpr.ptrB_bell_eq_mix2
#print axioms ErEpr.ptrB_disentangle_bell
#print axioms ErEpr.correlation_is_fuel
#print axioms ErEpr.negctrl_landauer_correlated

-- 觀測＝把線轉給儀器（ErEpr/Measurement.lean）
#print axioms ErEpr.plusProj_isHermitian
#print axioms ErEpr.plusProj_mul_self
#print axioms ErEpr.plusProj_posSemidef
#print axioms ErEpr.trace_plusProj
#print axioms ErEpr.vnEntropy_plusProj
#print axioms ErEpr.star_cnot
#print axioms ErEpr.cnot_mul_self
#print axioms ErEpr.cnot_star_mul
#print axioms ErEpr.cnot_measure
#print axioms ErEpr.ptrB_before
#print axioms ErEpr.ptrB_after
#print axioms ErEpr.measurement_dephases
#print axioms ErEpr.measurement_entropy
#print axioms ErEpr.measurement_total_entropy_conserved
#print axioms ErEpr.ptrB_local_conj
#print axioms ErEpr.local_cannot_undo
#print axioms ErEpr.pointer_cannot_undo
#print axioms ErEpr.joint_undo
#print axioms ErEpr.negctrl_local_no_decoherence

-- 一夫一妻（ErEpr/Monogamy.lean）
#print axioms ErEpr.exists_eq_conjTranspose_mul_self
#print axioms ErEpr.mul_eq_zero_of_trace_mul_eq_zero
#print axioms ErEpr.rankOne_mul_self
#print axioms ErEpr.rankOne_conjTranspose
#print axioms ErEpr.trace_rankOne
#print axioms ErEpr.rankOne_kron_one_conj
#print axioms ErEpr.monogamy
#print axioms ErEpr.ptrMid_kronecker
#print axioms ErEpr.ptrMid_kronecker3
#print axioms ErEpr.monogamy_mutualInfo
#print axioms ErEpr.maxEnt_posSemidef
#print axioms ErEpr.trace_maxEnt
#print axioms ErEpr.bell_rankOne_norm
#print axioms ErEpr.bell_monogamy
#print axioms ErEpr.bell_monogamy_witness
#print axioms ErEpr.negctrl_monogamy_mixed

-- 糾纏交換（ErEpr/Swapping.lean）
#print axioms ErEpr.mutualInfo_kronecker
#print axioms ErEpr.ptrBC_kronecker
#print axioms ErEpr.ptrBC_smul
#print axioms ErEpr.trace_ptrBC
#print axioms ErEpr.vecMulVec_kronecker
#print axioms ErEpr.bellPair_eq
#print axioms ErEpr.fin_two_one_add_one
#print axioms ErEpr.swapProj_mulVec
#print axioms ErEpr.vecMul_swapProj
#print axioms ErEpr.swap_post
#print axioms ErEpr.star_swapVec
#print axioms ErEpr.ptrBC_swapVec_00
#print axioms ErEpr.ptrBC_swapVec_01
#print axioms ErEpr.ptrBC_swapVec_10
#print axioms ErEpr.ptrBC_swapVec_11
#print axioms ErEpr.ptrBC_swapVec
#print axioms ErEpr.trace_bellAD
#print axioms ErEpr.bellAD_zero
#print axioms ErEpr.ptrBC_swap_post
#print axioms ErEpr.swap_prob
#print axioms ErEpr.swap_before
#print axioms ErEpr.entanglement_swapping
#print axioms ErEpr.swap_average_eq
#print axioms ErEpr.swap_average_no_signalling
#print axioms ErEpr.sepProj_mulVec
#print axioms ErEpr.vecMul_sepProj
#print axioms ErEpr.ptrBC_sepVec
#print axioms ErEpr.negctrl_swap_separate

-- 洞的形狀：AMPS 矛盾（ErEpr/Swapping.lean）、不可能定理的負控制（ErEpr/NoGo.lean）
#print axioms ErEpr.ptrFirst_kronecker
#print axioms ErEpr.ptrFirst_kronecker3
#print axioms ErEpr.amps_monogamy
#print axioms ErEpr.amps_contradiction
#print axioms ErEpr.ampsUnitaryState_posSemidef
#print axioms ErEpr.ptrFirst_ampsUnitaryState
#print axioms ErEpr.amps_each_half_satisfiable
#print axioms ErEpr.ghzState_posSemidef
#print axioms ErEpr.ptrFirst_ghzState
#print axioms ErEpr.ptrB_ptrFirst_ghzState
#print axioms ErEpr.ptrA_ptrFirst_ghzState
#print axioms ErEpr.mutualInfo_ptrFirst_ghzState
#print axioms ErEpr.negctrl_amps_mixed
#print axioms ErEpr.sum_twoTierDist
#print axioms ErEpr.sum_negMulLog_twoTierDist
#print axioms ErEpr.exists_twoTier_entropy
#print axioms ErEpr.exists_hamiltonian_gibbs_entropy_eq
#print axioms ErEpr.negctrl_nogo_varying_hamiltonian
#print axioms ErEpr.nogo_hinges_on_fixed_hamiltonian

-- 面積律（ErEpr/TensorNetwork.lean）
#print axioms ErEpr.cutEntropy_tnAmp_le
#print axioms ErEpr.cutMat_diag
#print axioms ErEpr.cutMat_diag_mul_conjTranspose
#print axioms ErEpr.trace_cutMat_diag
#print axioms ErEpr.cutEntropy_diag
#print axioms ErEpr.card_cutEdges_par
#print axioms ErEpr.tnAmp_parTN
#print axioms ErEpr.parC_mul_self
#print axioms ErEpr.area_law_saturated
#print axioms ErEpr.negctrl_nonlocal_entropy

-- Π 是完整的投影測量（ErEpr/Swapping.lean）
#print axioms ErEpr.star_bellSign
#print axioms ErEpr.bellVecBC_norm
#print axioms ErEpr.bellProjBC_mul_self
#print axioms ErEpr.bellProjBC_conjTranspose
#print axioms ErEpr.sum_bellProjBC
#print axioms ErEpr.swapProj_eq_reindex
#print axioms ErEpr.swapProj_isHermitian
#print axioms ErEpr.swapProj_mul_self
#print axioms ErEpr.sum_swapProj

-- 補印（2026-10-24）：tools/gen_index.py 發現原始碼裡有 theorem 宣告、但上面沒印到的輔助引理。
-- 它們多半是 `_apply`／線性性之類的小引理；主定理若用到它們，公理已經含在主定理的輸出裡，
-- 但沒被任何主定理用到的就從沒被機械查過——這裡全部補上。
-- Basic
#print axioms ErEpr.ptrB_apply
#print axioms ErEpr.ptrA_apply
#print axioms ErEpr.blk_apply
#print axioms ErEpr.blk_add
#print axioms ErEpr.blk_smul
#print axioms ErEpr.idKron_apply
#print axioms ErEpr.ptrB_idKron_apply
#print axioms ErEpr.vecOf_apply
#print axioms ErEpr.ptrB_add
#print axioms ErEpr.ptrB_smul
#print axioms ErEpr.ptrA_smul
#print axioms ErEpr.blk_kronecker
-- NoSignalling
#print axioms ErEpr.sandwich_apply
#print axioms ErEpr.trace_replace0
#print axioms ErEpr.transposeMap_apply
-- TFD
#print axioms ErEpr.nexp_ofReal
#print axioms ErEpr.nexp_pi_ofReal
#print axioms ErEpr.exp_neg_smul_diagonal
#print axioms ErEpr.ptrB_pureOf
#print axioms ErEpr.ptrA_pureOf
#print axioms ErEpr.conj_diag_mul_conj_diag
#print axioms ErEpr.conj_diag_conjTranspose
#print axioms ErEpr.conj_diag_mul_conj_diag'
#print axioms ErEpr.conj_diag_conjTranspose'
#print axioms ErEpr.kron_mulVec_vecOf
#print axioms ErEpr.eigU_star_mul
#print axioms ErEpr.eigU_mul_star
#print axioms ErEpr.eigU_spectral
#print axioms ErEpr.amp_star
#print axioms ErEpr.amp_sq
#print axioms ErEpr.tfdAmp_conjTranspose
#print axioms ErEpr.pauliY_isHermitian
#print axioms ErEpr.Vy_mul_VyInv
#print axioms ErEpr.VyInv_mul_Vy
#print axioms ErEpr.Vy_isUnit
#print axioms ErEpr.Vy_inv
#print axioms ErEpr.Vy_diag_VyInv
#print axioms ErEpr.neg_smul_pauliY
#print axioms ErEpr.exp_pauliY_01
#print axioms ErEpr.exp_pauliY_10
#print axioms ErEpr.commute_tfdAmp
#print axioms ErEpr.eigU_transpose_eq
#print axioms ErEpr.mapStar_transpose
#print axioms ErEpr.star_mapStar_mul
#print axioms ErEpr.wrong_mul_conjTranspose
#print axioms ErEpr.wrong_conjTranspose_mul_transpose
#print axioms ErEpr.H2_isHermitian
#print axioms ErEpr.gibbs_H2_neg_log2
#print axioms ErEpr.gibbs_H2_log4
-- MPS
#print axioms ErEpr.cutAt_mpsOpen
#print axioms ErEpr.cutAt_mpsRing
#print axioms ErEpr.mpsOpen_bell
#print axioms ErEpr.mpsRing_ringBell
#print axioms ErEpr.cutAt_ringBell
-- Entropy
#print axioms ErEpr.vnEntropy_smul_one
#print axioms ErEpr.rank_pos_of_posSemidef_trace_one
#print axioms ErEpr.roots_entropy_X_pow_mul
#print axioms ErEpr.vnEntropy_transpose
#print axioms ErEpr.cutAt_mpsOpen_smul
#print axioms ErEpr.sBell_mul_self
#print axioms ErEpr.cutAt_bellN_mul_conjTranspose
#print axioms ErEpr.chainProd_smul
#print axioms ErEpr.cutAt_ringBellN_mul_conjTranspose
-- ER
#print axioms ErEpr.hasDerivAt_affine
#print axioms ErEpr.areaIso_eq
-- Hawking
#print axioms ErEpr.continuous_properDist_integrand
#print axioms ErEpr.properDist_zero
#print axioms ErEpr.sqrtF_sub
-- TensorNetwork
#print axioms ErEpr.prod_split_mem
#print axioms ErEpr.sum_unit_fun
