# 定理索引（自動產生，勿手改）

由 `tools/gen_index.py` 從磁碟產生。重新產生：`/usr/bin/python3 -I tools/gen_index.py`。

- 公理來源：`evidence/er_epr_20261024T195146Z_lakebuild/axioms.out`
- 演習清單：`tools/drills_manifest.json`（95 份）；實際紅名單取每份演習最近一次重跑：`evidence/drills_20261024T192240Z`
- 定理總數：599（`theorem`／`lemma`，不含 `Axioms.lean`、`Coupling.lean`；不含 `def`、`example`）
- 公理狀態超出標準三公理的：0 條
- 沒有被 `Axioms.lean` 印出公理的定理：0 條

「演習（必須紅）」是清單上指定的；「實際紅」是最近一次重跑時，第一個失敗模組裡紅的宣告
（多半比指定的多，因為下游定理連帶紅）。「耦合斷言」⇒＝依賴閉包必須含右邊；⇏＝不得含。

## Basic（23 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `ptrB_apply` | [28](../ErEpr/Basic.lean#L28) | 標準三公理 |  |  |  |
| `ptrA_apply` | [35](../ErEpr/Basic.lean#L35) | 標準三公理 |  | R1 |  |
| `blk_apply` | [42](../ErEpr/Basic.lean#L42) | 標準三公理 |  |  |  |
| `blk_add` | [45](../ErEpr/Basic.lean#L45) | 標準三公理 |  |  |  |
| `blk_smul` | [49](../ErEpr/Basic.lean#L49) | 標準三公理 |  |  |  |
| `idKron_apply` | [61](../ErEpr/Basic.lean#L61) | 標準三公理 |  |  |  |
| `ptrB_idKron_apply` | [66](../ErEpr/Basic.lean#L66) | 標準三公理 | R2 | R1、R2 |  |
| `vecOf_apply` | [74](../ErEpr/Basic.lean#L74) | 標準三公理 |  |  |  |
| `ptrB_add` | [79](../ErEpr/Basic.lean#L79) | 標準三公理 |  |  |  |
| `ptrB_smul` | [82](../ErEpr/Basic.lean#L82) | 標準三公理 |  |  |  |
| `ptrA_smul` | [85](../ErEpr/Basic.lean#L85) | 標準三公理 |  |  |  |
| `trace_ptrB_mul` | [92](../ErEpr/Basic.lean#L92) | 標準三公理 | R1 | R1 |  |
| `ptrB_kronecker` | [100](../ErEpr/Basic.lean#L100) | 標準三公理 | R1 | R1 |  |
| `trace_ptrB` | [108](../ErEpr/Basic.lean#L108) | 標準三公理 |  |  |  |
| `ptrB_posSemidef` | [112](../ErEpr/Basic.lean#L112) | 標準三公理 |  | R1 |  |
| `ptrB_pure` | [122](../ErEpr/Basic.lean#L122) | 標準三公理 |  | R1 |  |
| `ptrA_pure` | [129](../ErEpr/Basic.lean#L129) | 標準三公理 |  |  |  |
| `ptrB_maxEnt` | [144](../ErEpr/Basic.lean#L144) | 標準三公理 |  |  |  |
| `ptrA_maxEnt` | [148](../ErEpr/Basic.lean#L148) | 標準三公理 |  |  |  |
| `ptrB_ne_ptrA_witness` | [154](../ErEpr/Basic.lean#L154) | 標準三公理 |  |  |  |
| `blk_kronecker` | [163](../ErEpr/Basic.lean#L163) | 標準三公理 |  |  |  |
| `idKron_kronecker` | [168](../ErEpr/Basic.lean#L168) | 標準三公理 | R2 | R2 |  |
| `idKron_unique` | [175](../ErEpr/Basic.lean#L175) | 標準三公理 |  |  |  |

## NoSignalling（20 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `ptrB_idKron` | [30](../ErEpr/NoSignalling.lean#L30) | 標準三公理 | R3 | R3 | ⇏ idKron_unique |
| `sandwich_apply` | [46](../ErEpr/NoSignalling.lean#L46) | 標準三公理 |  |  |  |
| `trace_sandwich` | [50](../ErEpr/NoSignalling.lean#L50) | 標準三公理 |  |  |  |
| `sandwich_one_kron` | [58](../ErEpr/NoSignalling.lean#L58) | 標準三公理 |  |  |  |
| `Kraus.trace_toLin` | [78](../ErEpr/NoSignalling.lean#L78) | 標準三公理 | R3b | R3b |  |
| `Kraus.app_eq_idKron` | [86](../ErEpr/NoSignalling.lean#L86) | 標準三公理 |  |  |  |
| `Kraus.no_signalling` | [90](../ErEpr/NoSignalling.lean#L90) | 標準三公理 |  | CP3、R3 | ⇒ ptrB_idKron idKron_unique |
| `negctrl_not_tp` | [100](../ErEpr/NoSignalling.lean#L100) | 標準三公理 |  |  |  |
| `kUnital_unital` | [111](../ErEpr/NoSignalling.lean#L111) | 標準三公理 |  |  |  |
| `kUnital_not_tp` | [116](../ErEpr/NoSignalling.lean#L116) | 標準三公理 |  |  |  |
| `negctrl_unital_not_tp` | [123](../ErEpr/NoSignalling.lean#L123) | 標準三公理 |  |  |  |
| `trace_replace0` | [139](../ErEpr/NoSignalling.lean#L139) | 標準三公理 |  |  |  |
| `negctrl_replace_changes_ptrA` | [144](../ErEpr/NoSignalling.lean#L144) | 標準三公理 |  | R3 |  |
| `negctrl_A_side_changes_ptrB` | [155](../ErEpr/NoSignalling.lean#L155) | 標準三公理 |  |  |  |
| `ampK_not_unital` | [186](../ErEpr/NoSignalling.lean#L186) | 標準三公理 |  |  |  |
| `witness_pauliX` | [193](../ErEpr/NoSignalling.lean#L193) | 標準三公理 |  |  |  |
| `witness_amplitudeDamping` | [197](../ErEpr/NoSignalling.lean#L197) | 標準三公理 |  |  |  |
| `witness_transpose` | [210](../ErEpr/NoSignalling.lean#L210) | 標準三公理 |  | R3 |  |
| `transposeMap_apply` | [215](../ErEpr/NoSignalling.lean#L215) | 標準三公理 |  |  |  |
| `transposeMap_not_completelyPositive` | [223](../ErEpr/NoSignalling.lean#L223) | 標準三公理 | R19 | R19 |  |

## TFD（69 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `nexp_ofReal` | [45](../ErEpr/TFD.lean#L45) | 標準三公理 |  |  |  |
| `nexp_pi_ofReal` | [50](../ErEpr/TFD.lean#L50) | 標準三公理 |  |  |  |
| `exp_neg_smul_diagonal` | [57](../ErEpr/TFD.lean#L57) | 標準三公理 |  |  |  |
| `gibbs_diagonal_real` | [65](../ErEpr/TFD.lean#L65) | 標準三公理 | R5 | R5 |  |
| `ptrB_pureOf` | [80](../ErEpr/TFD.lean#L80) | 標準三公理 |  |  |  |
| `ptrA_pureOf` | [85](../ErEpr/TFD.lean#L85) | 標準三公理 |  |  |  |
| `trace_pureOf` | [91](../ErEpr/TFD.lean#L91) | 標準三公理 |  |  |  |
| `conj_diag_mul_conj_diag` | [96](../ErEpr/TFD.lean#L96) | 標準三公理 |  |  |  |
| `conj_diag_conjTranspose` | [105](../ErEpr/TFD.lean#L105) | 標準三公理 |  |  |  |
| `conj_diag_mul_conj_diag'` | [111](../ErEpr/TFD.lean#L111) | 標準三公理 |  |  |  |
| `conj_diag_conjTranspose'` | [120](../ErEpr/TFD.lean#L120) | 標準三公理 |  |  |  |
| `kron_mulVec_vecOf` | [127](../ErEpr/TFD.lean#L127) | 標準三公理 |  |  |  |
| `vecOf_mul` | [137](../ErEpr/TFD.lean#L137) | 標準三公理 |  |  |  |
| `eigU_star_mul` | [148](../ErEpr/TFD.lean#L148) | 標準三公理 |  |  |  |
| `eigU_mul_star` | [151](../ErEpr/TFD.lean#L151) | 標準三公理 |  |  |  |
| `eigU_spectral` | [155](../ErEpr/TFD.lean#L155) | 標準三公理 |  |  |  |
| `exp_neg_smul_eigen` | [162](../ErEpr/TFD.lean#L162) | 標準三公理 |  |  |  |
| `trace_exp_neg_smul_ne_zero` | [177](../ErEpr/TFD.lean#L177) | 標準三公理 |  |  |  |
| `amp_star` | [197](../ErEpr/TFD.lean#L197) | 標準三公理 |  |  |  |
| `amp_sq` | [203](../ErEpr/TFD.lean#L203) | 標準三公理 |  |  |  |
| `vecOf_tfdAmp` | [214](../ErEpr/TFD.lean#L214) | 標準三公理 |  | R4、R6 |  |
| `tfdAmp_conjTranspose` | [223](../ErEpr/TFD.lean#L223) | 標準三公理 | R4、R6 | R4、R6 |  |
| `tfdAmp_mul_conjTranspose` | [232](../ErEpr/TFD.lean#L232) | 標準三公理 | R4 | R4、R6 |  |
| `tfdAmp_eq_exp` | [249](../ErEpr/TFD.lean#L249) | 標準三公理 | E1 | E1、R4、R6 |  |
| `exp_half_mul_conjTranspose` | [260](../ErEpr/TFD.lean#L260) | 標準三公理 |  |  |  |
| `tfdAmp_mul_conjTranspose'` | [275](../ErEpr/TFD.lean#L275) | 標準三公理 |  | E1 |  |
| `tfdAmp_isUnit` | [280](../ErEpr/TFD.lean#L280) | 標準三公理 |  |  |  |
| `purification_unique_of_isUnit` | [291](../ErEpr/TFD.lean#L291) | 標準三公理 | P1 | P1 |  |
| `tfd_purification_unique` | [303](../ErEpr/TFD.lean#L303) | 標準三公理 |  | P1 |  |
| `ptrB_tfdState` | [310](../ErEpr/TFD.lean#L310) | 標準三公理 |  | R5 | ⇒ tfdAmp_mul_conjTranspose exp_neg_smul_eigen |
| `ptrA_tfdState` | [314](../ErEpr/TFD.lean#L314) | 標準三公理 |  | R5 |  |
| `trace_tfdState` | [321](../ErEpr/TFD.lean#L321) | 標準三公理 |  |  |  |
| `pauliY_isHermitian` | [330](../ErEpr/TFD.lean#L330) | 標準三公理 |  |  |  |
| `Vy_mul_VyInv` | [339](../ErEpr/TFD.lean#L339) | 標準三公理 |  |  |  |
| `VyInv_mul_Vy` | [344](../ErEpr/TFD.lean#L344) | 標準三公理 |  |  |  |
| `Vy_isUnit` | [349](../ErEpr/TFD.lean#L349) | 標準三公理 |  |  |  |
| `Vy_inv` | [351](../ErEpr/TFD.lean#L351) | 標準三公理 |  |  |  |
| `Vy_diag_VyInv` | [354](../ErEpr/TFD.lean#L354) | 標準三公理 |  |  |  |
| `neg_smul_pauliY` | [362](../ErEpr/TFD.lean#L362) | 標準三公理 |  |  |  |
| `exp_neg_smul_pauliY` | [370](../ErEpr/TFD.lean#L370) | 標準三公理 |  |  |  |
| `exp_pauliY_01` | [375](../ErEpr/TFD.lean#L375) | 標準三公理 |  |  |  |
| `exp_pauliY_10` | [384](../ErEpr/TFD.lean#L384) | 標準三公理 |  |  |  |
| `gibbs_pauliY_ne_transpose` | [395](../ErEpr/TFD.lean#L395) | 標準三公理 |  | R5 |  |
| `negctrl_ptrA_ne_gibbs` | [411](../ErEpr/TFD.lean#L411) | 標準三公理 |  |  |  |
| `commute_tfdAmp` | [419](../ErEpr/TFD.lean#L419) | 標準三公理 |  | R4 |  |
| `tfd_boost_invariant` | [434](../ErEpr/TFD.lean#L434) | 標準三公理 | R20 | R20 |  |
| `boost_mulVec_vecOf` | [440](../ErEpr/TFD.lean#L440) | 標準三公理 |  |  |  |
| `boost_invariant_iff_commute` | [451](../ErEpr/TFD.lean#L451) | 標準三公理 |  |  |  |
| `boost_invariant_one` | [465](../ErEpr/TFD.lean#L465) | 標準三公理 |  |  |  |
| `tfdAmp_zero` | [470](../ErEpr/TFD.lean#L470) | 標準三公理 |  | R4、R6 |  |
| `tfd_boost_invariant_zero` | [479](../ErEpr/TFD.lean#L479) | 標準三公理 |  | R20 |  |
| `eigU_transpose_eq` | [493](../ErEpr/TFD.lean#L493) | 標準三公理 |  |  |  |
| `mapStar_transpose` | [497](../ErEpr/TFD.lean#L497) | 標準三公理 |  |  |  |
| `star_mapStar_mul` | [499](../ErEpr/TFD.lean#L499) | 標準三公理 |  |  |  |
| `wrong_mul_conjTranspose` | [506](../ErEpr/TFD.lean#L506) | 標準三公理 |  |  |  |
| `wrong_conjTranspose_mul_transpose` | [511](../ErEpr/TFD.lean#L511) | 標準三公理 |  |  |  |
| `ptrB_pureOf_wrong` | [519](../ErEpr/TFD.lean#L519) | 標準三公理 |  | R5 |  |
| `ptrA_pureOf_wrong` | [524](../ErEpr/TFD.lean#L524) | 標準三公理 |  | R5 |  |
| `negctrl_wrong_amplitude` | [529](../ErEpr/TFD.lean#L529) | 標準三公理 |  |  |  |
| `tfdAmpWrong_eq` | [540](../ErEpr/TFD.lean#L540) | 標準三公理 |  | R4、R6 |  |
| `eigU_mul_transpose_unitary` | [546](../ErEpr/TFD.lean#L546) | 標準三公理 |  |  |  |
| `vecOf_tfdAmpWrong` | [557](../ErEpr/TFD.lean#L557) | 標準三公理 |  |  |  |
| `H2_isHermitian` | [567](../ErEpr/TFD.lean#L567) | 標準三公理 |  |  |  |
| `gibbs_H2_log2` | [572](../ErEpr/TFD.lean#L572) | 標準三公理 |  |  |  |
| `gibbs_H2_neg_log2` | [581](../ErEpr/TFD.lean#L581) | 標準三公理 |  |  |  |
| `gibbs_H2_log4` | [590](../ErEpr/TFD.lean#L590) | 標準三公理 |  |  |  |
| `negctrl_sign_flip` | [599](../ErEpr/TFD.lean#L599) | 標準三公理 |  |  |  |
| `negctrl_missing_half` | [608](../ErEpr/TFD.lean#L608) | 標準三公理 |  |  |  |
| `negctrl_tfdAmp_full_beta` | [617](../ErEpr/TFD.lean#L617) | 標準三公理 |  | E1 |  |

## MPS（13 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `chainProd_append` | [55](../ErEpr/MPS.lean#L55) | 標準三公理 | R9 | R9 |  |
| `cutAt_mpsOpen` | [68](../ErEpr/MPS.lean#L68) | 標準三公理 |  |  |  |
| `rank_cutAt_mpsOpen_le` | [81](../ErEpr/MPS.lean#L81) | 標準三公理 | R7 | R7 |  |
| `cutAt_mpsRing` | [93](../ErEpr/MPS.lean#L93) | 標準三公理 |  |  |  |
| `rank_cutAt_mpsRing_le` | [104](../ErEpr/MPS.lean#L104) | 標準三公理 | R8 | R8 |  |
| `rank_ptrB_pure` | [114](../ErEpr/MPS.lean#L114) | 標準三公理 |  |  |  |
| `rank_ptrB_mpsOpen_le` | [119](../ErEpr/MPS.lean#L119) | 標準三公理 |  | R7 |  |
| `mpsOpen_bell` | [136](../ErEpr/MPS.lean#L136) | 標準三公理 |  | R9 |  |
| `cutAt_bell` | [145](../ErEpr/MPS.lean#L145) | 標準三公理 |  |  |  |
| `rank_cutAt_bell` | [155](../ErEpr/MPS.lean#L155) | 標準三公理 |  |  |  |
| `mpsRing_ringBell` | [167](../ErEpr/MPS.lean#L167) | 標準三公理 |  |  |  |
| `cutAt_ringBell` | [178](../ErEpr/MPS.lean#L178) | 標準三公理 |  |  |  |
| `rank_cutAt_ringBell` | [188](../ErEpr/MPS.lean#L188) | 標準三公理 |  |  |  |

## Entropy（27 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `vnEntropy_eq_sum_eigenvalues` | [47](../ErEpr/Entropy.lean#L47) | 標準三公理 | R11 | R11 |  |
| `vnEntropy_diagonal` | [53](../ErEpr/Entropy.lean#L53) | 標準三公理 | R11 | R11 |  |
| `vnEntropy_smul_one` | [62](../ErEpr/Entropy.lean#L62) | 標準三公理 |  |  |  |
| `vnEntropy_maxMixed` | [68](../ErEpr/Entropy.lean#L68) | 標準三公理 |  |  |  |
| `vnEntropy_ptrB_maxEnt` | [76](../ErEpr/Entropy.lean#L76) | 標準三公理 |  |  |  |
| `rank_pos_of_posSemidef_trace_one` | [85](../ErEpr/Entropy.lean#L85) | 標準三公理 |  |  |  |
| `vnEntropy_le_log_rank` | [99](../ErEpr/Entropy.lean#L99) | 標準三公理 | R10 | R10 |  |
| `vnEntropy_le_log_of_rank_le` | [146](../ErEpr/Entropy.lean#L146) | 標準三公理 |  | R10 |  |
| `negctrl_unnormalized` | [154](../ErEpr/Entropy.lean#L154) | 標準三公理 |  |  |  |
| `roots_entropy_X_pow_mul` | [174](../ErEpr/Entropy.lean#L174) | 標準三公理 |  |  |  |
| `vnEntropy_mul_comm` | [183](../ErEpr/Entropy.lean#L183) | 標準三公理 |  | R11 |  |
| `vnEntropy_transpose` | [189](../ErEpr/Entropy.lean#L189) | 標準三公理 |  |  |  |
| `vnEntropy_ptrA_pureOf_eq` | [194](../ErEpr/Entropy.lean#L194) | 標準三公理 |  |  |  |
| `vnEntropy_ptrA_tfdState` | [201](../ErEpr/Entropy.lean#L201) | 標準三公理 |  |  |  |
| `vnEntropy_cut_mpsOpen_le` | [210](../ErEpr/Entropy.lean#L210) | 標準三公理 |  |  | ⇒ rank_cutAt_mpsOpen_le vnEntropy_le_log_rank chainProd_append |
| `vnEntropy_cut_mpsRing_le` | [221](../ErEpr/Entropy.lean#L221) | 標準三公理 | R12 | R12 |  |
| `cutAt_mpsOpen_smul` | [233](../ErEpr/Entropy.lean#L233) | 標準三公理 |  |  |  |
| `sBell_mul_self` | [242](../ErEpr/Entropy.lean#L242) | 標準三公理 |  |  |  |
| `cutAt_bellN_mul_conjTranspose` | [246](../ErEpr/Entropy.lean#L246) | 標準三公理 |  |  |  |
| `trace_bellN` | [255](../ErEpr/Entropy.lean#L255) | 標準三公理 |  |  |  |
| `vnEntropy_cut_bellN` | [261](../ErEpr/Entropy.lean#L261) | 標準三公理 |  |  |  |
| `chainProd_smul` | [271](../ErEpr/Entropy.lean#L271) | 標準三公理 |  |  |  |
| `cutAt_mpsRing_smul` | [283](../ErEpr/Entropy.lean#L283) | 標準三公理 |  |  |  |
| `cutAt_ringBellN` | [290](../ErEpr/Entropy.lean#L290) | 標準三公理 |  |  |  |
| `cutAt_ringBellN_mul_conjTranspose` | [299](../ErEpr/Entropy.lean#L299) | 標準三公理 |  |  |  |
| `trace_ringBellN` | [309](../ErEpr/Entropy.lean#L309) | 標準三公理 |  |  |  |
| `vnEntropy_cut_ringBellN` | [316](../ErEpr/Entropy.lean#L316) | 標準三公理 |  |  |  |

## NoGo（37 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `partZ_nonneg` | [70](../ErEpr/NoGo.lean#L70) | 標準三公理 |  |  |  |
| `partZ_pos` | [73](../ErEpr/NoGo.lean#L73) | 標準三公理 |  |  |  |
| `trace_exp_neg_smul_eq` | [79](../ErEpr/NoGo.lean#L79) | 標準三公理 |  |  |  |
| `gibbs_eq_conj` | [86](../ErEpr/NoGo.lean#L86) | 標準三公理 |  |  |  |
| `vnEntropy_unitary_conj` | [100](../ErEpr/NoGo.lean#L100) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs` | [105](../ErEpr/NoGo.lean#L105) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_eq_fn` | [111](../ErEpr/NoGo.lean#L111) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_nonneg` | [130](../ErEpr/NoGo.lean#L130) | 標準三公理 |  |  |  |
| `hasDerivAt_bw` | [142](../ErEpr/NoGo.lean#L142) | 標準三公理 |  |  |  |
| `hasDerivAt_partZ` | [151](../ErEpr/NoGo.lean#L151) | 標準三公理 |  |  |  |
| `hasDerivAt_partN` | [158](../ErEpr/NoGo.lean#L158) | 標準三公理 |  |  |  |
| `hasDerivAt_gibbsEntropyFn` | [167](../ErEpr/NoGo.lean#L167) | 標準三公理 |  |  |  |
| `sq_sum_le_mul_sum` | [181](../ErEpr/NoGo.lean#L181) | 標準三公理 |  |  |  |
| `energyVar_nonneg` | [194](../ErEpr/NoGo.lean#L194) | 標準三公理 |  |  |  |
| `antitoneOn_gibbsEntropyFn` | [205](../ErEpr/NoGo.lean#L205) | 標準三公理 | NG1 | NG1 | ⇏ hawking_beta first_law_area |
| `no_gibbs_entropy_strictMonoOn` | [220](../ErEpr/NoGo.lean#L220) | 標準三公理 |  | NG1 |  |
| `no_finite_dim_gibbs_matches_bh` | [241](../ErEpr/NoGo.lean#L241) | 標準三公理 | NG2 | NG2 | ⇏ hawking_beta first_law_area conicalRatio |
| `no_finite_dim_gibbs_matches_bh_mass` | [257](../ErEpr/NoGo.lean#L257) | 標準三公理 |  | NG2 |  |
| `gibbs_zero` | [275](../ErEpr/NoGo.lean#L275) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_zero` | [282](../ErEpr/NoGo.lean#L282) | 標準三公理 |  |  |  |
| `gibbsEntropyFn_zero` | [287](../ErEpr/NoGo.lean#L287) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_le_log_card` | [292](../ErEpr/NoGo.lean#L292) | 標準三公理 |  | NG1 |  |
| `gibbs_posSemidef` | [298](../ErEpr/NoGo.lean#L298) | 標準三公理 |  |  |  |
| `trace_gibbs` | [304](../ErEpr/NoGo.lean#L304) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_le_log_card_of_rank` | [309](../ErEpr/NoGo.lean#L309) | 標準三公理 |  |  |  |
| `negctrl_single_point` | [319](../ErEpr/NoGo.lean#L319) | 標準三公理 |  |  |  |
| `negctrl_single_point_H2` | [350](../ErEpr/NoGo.lean#L350) | 標準三公理 |  |  |  |
| `trace_gibbs_mul_self` | [360](../ErEpr/NoGo.lean#L360) | 標準三公理 |  |  |  |
| `hasDerivAt_energyMean` | [371](../ErEpr/NoGo.lean#L371) | 標準三公理 | S5 | S5 |  |
| `gibbs_dS_eq_beta_dE` | [383](../ErEpr/NoGo.lean#L383) | 標準三公理 | S5 | S5 | ⇒ hasDerivAt_gibbsEntropyFn hasDerivAt_energyMean |
| `gibbs_entropy_energy_slope` | [389](../ErEpr/NoGo.lean#L389) | 標準三公理 |  |  |  |
| `sum_twoTierDist` | [404](../ErEpr/NoGo.lean#L404) | 標準三公理 |  |  |  |
| `sum_negMulLog_twoTierDist` | [413](../ErEpr/NoGo.lean#L413) | 標準三公理 |  |  |  |
| `exists_twoTier_entropy` | [423](../ErEpr/NoGo.lean#L423) | 標準三公理 |  |  |  |
| `exists_hamiltonian_gibbs_entropy_eq` | [448](../ErEpr/NoGo.lean#L448) | 標準三公理 | NG6 | NG6 |  |
| `negctrl_nogo_varying_hamiltonian` | [477](../ErEpr/NoGo.lean#L477) | 標準三公理 | NG5 | NG5、NG6 | ⇒ ；⇏  |
| `nogo_hinges_on_fixed_hamiltonian` | [496](../ErEpr/NoGo.lean#L496) | 標準三公理 |  | NG2、NG5 | ⇒  |

## Klein（22 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `kleinGap_nonneg` | [48](../ErEpr/Klein.lean#L48) | 標準三公理 | KL2 | KL2 |  |
| `kleinGap_pos` | [64](../ErEpr/Klein.lean#L64) | 標準三公理 | KL2 | KL2 |  |
| `klein_sum_identity` | [82](../ErEpr/Klein.lean#L82) | 標準三公理 | KL5 | KL2、KL5 |  |
| `klein_real` | [114](../ErEpr/Klein.lean#L114) | 標準三公理 |  | KL5 |  |
| `nonempty_of_trace_eq_one` | [142](../ErEpr/Klein.lean#L142) | 標準三公理 |  |  |  |
| `sum_normSq_row` | [155](../ErEpr/Klein.lean#L155) | 標準三公理 |  |  |  |
| `sum_normSq_col` | [166](../ErEpr/Klein.lean#L166) | 標準三公理 |  |  |  |
| `trace_diag_mul_diag` | [177](../ErEpr/Klein.lean#L177) | 標準三公理 |  |  |  |
| `eigU_cross_mul_star` | [192](../ErEpr/Klein.lean#L192) | 標準三公理 |  |  |  |
| `eigU_cross_star_mul` | [198](../ErEpr/Klein.lean#L198) | 標準三公理 |  |  |  |
| `trace_mul_eq_sum` | [204](../ErEpr/Klein.lean#L204) | 標準三公理 |  |  |  |
| `sum_eigenvalues_of_trace_eq_one` | [219](../ErEpr/Klein.lean#L219) | 標準三公理 |  |  |  |
| `klein_gap_eq` | [231](../ErEpr/Klein.lean#L231) | 標準三公理 |  |  |  |
| `vnEntropy_le_beta_energy_add_log` | [244](../ErEpr/Klein.lean#L244) | 標準三公理 | KL1、KL3 | KL1、KL3 | ⇒ ；⇏ vnEntropy_gibbs_eq_fn hawking_beta first_law_area |
| `vnEntropy_eq_beta_energy_add_log_iff` | [258](../ErEpr/Klein.lean#L258) | 標準三公理 | KL4 | KL4 | ⇒  |
| `vnEntropy_gibbs_eq_beta_energy_add_log` | [310](../ErEpr/Klein.lean#L310) | 標準三公理 |  | KL4 |  |
| `vnEntropy_le_gibbs_of_energy_eq` | [315](../ErEpr/Klein.lean#L315) | 標準三公理 |  | KL1、KL3 |  |
| `vnEntropy_lt_gibbs_of_energy_eq` | [324](../ErEpr/Klein.lean#L324) | 標準三公理 |  | KL1、KL3、KL4 |  |
| `ket0Proj_posSemidef` | [338](../ErEpr/Klein.lean#L338) | 標準三公理 |  |  |  |
| `trace_ket0Proj` | [341](../ErEpr/Klein.lean#L341) | 標準三公理 |  |  |  |
| `negctrl_klein_pure_H2` | [346](../ErEpr/Klein.lean#L346) | 標準三公理 |  | KL1、KL3、KL4 | ⇒ vnEntropy_eq_beta_energy_add_log_iff gibbs_H2_log2 |
| `negctrl_klein_other_beta_H2` | [360](../ErEpr/Klein.lean#L360) | 標準三公理 |  | KL1、KL3、KL4 |  |

## ER（13 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `FutureCausal.nonneg` | [39](../ErEpr/ER.lean#L39) | 標準三公理 | R13 | R13 |  |
| `kruskal_monotone` | [57](../ErEpr/ER.lean#L57) | 標準三公理 |  |  |  |
| `no_causal_curve_between_exteriors` | [83](../ErEpr/ER.lean#L83) | 標準三公理 |  |  |  |
| `hasDerivAt_affine` | [101](../ErEpr/ER.lean#L101) | 標準三公理 |  |  |  |
| `meet_in_interior` | [107](../ErEpr/ER.lean#L107) | 標準三公理 |  |  |  |
| `bridge_slice_spacelike` | [119](../ErEpr/ER.lean#L119) | 標準三公理 |  |  |  |
| `negctrl_spacelike_connects` | [133](../ErEpr/ER.lean#L133) | 標準三公理 |  |  |  |
| `areaIso_eq` | [152](../ErEpr/ER.lean#L152) | 標準三公理 |  |  |  |
| `throat_area_le` | [157](../ErEpr/ER.lean#L157) | 標準三公理 | R14 | R14 |  |
| `throat_area_eq` | [165](../ErEpr/ER.lean#L165) | 標準三公理 |  |  |  |
| `hasDerivAt_inversion` | [171](../ErEpr/ER.lean#L171) | 標準三公理 |  |  |  |
| `inversion_isometry` | [183](../ErEpr/ER.lean#L183) | 標準三公理 | R15 | R15 |  |
| `inversion_fixed` | [189](../ErEpr/ER.lean#L189) | 標準三公理 |  |  |  |

## Hawking（14 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `continuous_properDist_integrand` | [41](../ErEpr/Hawking.lean#L41) | 標準三公理 |  |  |  |
| `properDist_hasDerivAt` | [45](../ErEpr/Hawking.lean#L45) | 標準三公理 | R16 | R16 |  |
| `properDist_zero` | [49](../ErEpr/Hawking.lean#L49) | 標準三公理 |  |  |  |
| `properDist_r_hasDerivAt` | [52](../ErEpr/Hawking.lean#L52) | 標準三公理 |  |  |  |
| `conicalRatio_eq_coneAngleRatio` | [78](../ErEpr/Hawking.lean#L78) | 標準三公理 |  |  |  |
| `coneAngleRatio_cone` | [85](../ErEpr/Hawking.lean#L85) | 標準三公理 | NG4 | NG4 |  |
| `coneAngleRatio_cone_not_unit` | [94](../ErEpr/Hawking.lean#L94) | 標準三公理 |  | NG4 |  |
| `sqrtF_sub` | [102](../ErEpr/Hawking.lean#L102) | 標準三公理 |  |  |  |
| `conicalRatio_tendsto` | [109](../ErEpr/Hawking.lean#L109) | 標準三公理 | R17 | R17 |  |
| `hawking_beta` | [147](../ErEpr/Hawking.lean#L147) | 標準三公理 | COUPLE | COUPLE、R17 |  |
| `negctrl_wrong_beta` | [160](../ErEpr/Hawking.lean#L160) | 標準三公理 |  | R17 |  |
| `first_law_area` | [181](../ErEpr/Hawking.lean#L181) | 標準三公理 | R18、COUPLE | COUPLE、R18 | ⇒ hawking_beta conicalRatio_tendsto |
| `first_law_witness` | [202](../ErEpr/Hawking.lean#L202) | 標準三公理 |  | COUPLE |  |
| `negctrl_first_law_const` | [213](../ErEpr/Hawking.lean#L213) | 標準三公理 | NG3 | COUPLE、NG3 |  |

## TensorNetwork（28 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `inW_of_inc_mem` | [82](../ErEpr/TensorNetwork.lean#L82) | 標準三公理 | TN1b | TN1b |  |
| `not_inW_of_inc_nmem` | [93](../ErEpr/TensorNetwork.lean#L93) | 標準三公理 | TN1b | TN1b |  |
| `prod_split_mem` | [121](../ErEpr/TensorNetwork.lean#L121) | 標準三公理 |  |  |  |
| `cutMat_tnAmp` | [126](../ErEpr/TensorNetwork.lean#L126) | 標準三公理 |  |  |  |
| `rank_cutMat_tnAmp_le` | [160](../ErEpr/TensorNetwork.lean#L160) | 標準三公理 | TN1a、TN2、TN3 | TN1a、TN2、TN3 | ⇒ cutMat_tnAmp |
| `sum_unit_fun` | [187](../ErEpr/TensorNetwork.lean#L187) | 標準三公理 |  |  |  |
| `tnAmp_path2TN` | [192](../ErEpr/TensorNetwork.lean#L192) | 標準三公理 |  |  |  |
| `tnAmp_bellTN` | [208](../ErEpr/TensorNetwork.lean#L208) | 標準三公理 |  |  |  |
| `card_cutEdges_path2` | [214](../ErEpr/TensorNetwork.lean#L214) | 標準三公理 |  | TN3 |  |
| `rank_cutMat_bellTN` | [218](../ErEpr/TensorNetwork.lean#L218) | 標準三公理 |  | TN1a、TN2 |  |
| `tnAmp_ring2TN` | [248](../ErEpr/TensorNetwork.lean#L248) | 標準三公理 |  |  |  |
| `tnAmp_ringBellTN` | [263](../ErEpr/TensorNetwork.lean#L263) | 標準三公理 |  |  |  |
| `card_cutEdges_ring2` | [269](../ErEpr/TensorNetwork.lean#L269) | 標準三公理 |  | TN3 |  |
| `rank_cutMat_ringBellTN` | [273](../ErEpr/TensorNetwork.lean#L273) | 標準三公理 |  | TN1a、TN2 |  |
| `card_cutEdges_loop` | [299](../ErEpr/TensorNetwork.lean#L299) | 標準三公理 |  | TN3 |  |
| `rank_cutMat_loop_le` | [303](../ErEpr/TensorNetwork.lean#L303) | 標準三公理 |  | TN1a |  |
| `tnAmpAll_loopT` | [311](../ErEpr/TensorNetwork.lean#L311) | 標準三公理 |  |  |  |
| `negctrl_nonlocal_tensor` | [320](../ErEpr/TensorNetwork.lean#L320) | 標準三公理 |  |  |  |
| `cutEntropy_tnAmp_le` | [345](../ErEpr/TensorNetwork.lean#L345) | 標準三公理 | AL1、AL2 | AL1、AL2、TN1a、TN2 | ⇒ rank_cutMat_tnAmp_le vnEntropy_le_log_rank |
| `cutMat_diag` | [382](../ErEpr/TensorNetwork.lean#L382) | 標準三公理 |  |  |  |
| `cutMat_diag_mul_conjTranspose` | [389](../ErEpr/TensorNetwork.lean#L389) | 標準三公理 |  |  |  |
| `trace_cutMat_diag` | [401](../ErEpr/TensorNetwork.lean#L401) | 標準三公理 |  |  |  |
| `cutEntropy_diag` | [412](../ErEpr/TensorNetwork.lean#L412) | 標準三公理 |  |  |  |
| `card_cutEdges_par` | [428](../ErEpr/TensorNetwork.lean#L428) | 標準三公理 |  | TN3 |  |
| `tnAmp_parTN` | [440](../ErEpr/TensorNetwork.lean#L440) | 標準三公理 |  |  |  |
| `parC_mul_self` | [459](../ErEpr/TensorNetwork.lean#L459) | 標準三公理 |  |  |  |
| `area_law_saturated` | [465](../ErEpr/TensorNetwork.lean#L465) | 標準三公理 |  |  | ⇏ cutEntropy_tnAmp_le rank_cutMat_tnAmp_le |
| `negctrl_nonlocal_entropy` | [484](../ErEpr/TensorNetwork.lean#L484) | 標準三公理 |  |  | ⇏ cutEntropy_tnAmp_le rank_cutMat_tnAmp_le |

## Chain（3 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `ptrB_idKron_tfdState` | [33](../ErEpr/Chain.lean#L33) | 標準三公理 |  |  | ⇒ ptrB_idKron ptrB_tfdState |
| `no_gibbs_matches_unitConeAngle` | [42](../ErEpr/Chain.lean#L42) | 標準三公理 |  |  | ⇒ hawking_beta no_finite_dim_gibbs_matches_bh_mass |
| `no_gibbs_matches_first_law` | [56](../ErEpr/Chain.lean#L56) | 標準三公理 |  |  | ⇒  |

## KMS（19 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `exp_neg_mul_exp` | [40](../ErEpr/KMS.lean#L40) | 標準三公理 |  |  |  |
| `exp_mul_exp_neg` | [46](../ErEpr/KMS.lean#L46) | 標準三公理 |  |  |  |
| `exp_smul_diagonal` | [52](../ErEpr/KMS.lean#L52) | 標準三公理 |  |  |  |
| `conj_mul_conj` | [67](../ErEpr/KMS.lean#L67) | 標準三公理 |  |  |  |
| `nuStep_mul` | [75](../ErEpr/KMS.lean#L75) | 標準三公理 |  |  |  |
| `nuStep_one` | [80](../ErEpr/KMS.lean#L80) | 標準三公理 |  |  |  |
| `nuStepAlgHom_apply` | [93](../ErEpr/KMS.lean#L93) | 標準三公理 |  |  |  |
| `conj_eq_self_iff` | [97](../ErEpr/KMS.lean#L97) | 標準三公理 |  |  |  |
| `trace_conj_cycle` | [114](../ErEpr/KMS.lean#L114) | 標準三公理 |  |  |  |
| `gibbs_isKMS` | [121](../ErEpr/KMS.lean#L121) | 標準三公理 | K1 | K1 |  |
| `kms_core` | [128](../ErEpr/KMS.lean#L128) | 標準三公理 |  |  |  |
| `isKMS_unique` | [157](../ErEpr/KMS.lean#L157) | 標準三公理 | K1、K2 | K1、K2 |  |
| `isKMS_iff_eq_gibbs` | [162](../ErEpr/KMS.lean#L162) | 標準三公理 |  | K2 |  |
| `gibbs_transpose` | [171](../ErEpr/KMS.lean#L171) | 標準三公理 |  |  |  |
| `tfd_ptrB_isKMS` | [176](../ErEpr/KMS.lean#L176) | 標準三公理 |  |  |  |
| `tfd_ptrA_isKMS` | [182](../ErEpr/KMS.lean#L182) | 標準三公理 |  |  | ⇒ ptrA_tfdState gibbs_isKMS |
| `diagonal_mul_single_mul_diagonal` | [190](../ErEpr/KMS.lean#L190) | 標準三公理 |  |  |  |
| `negctrl_scalar_not_kms` | [202](../ErEpr/KMS.lean#L202) | 標準三公理 |  | K1 |  |
| `negctrl_maxMixed_not_kms` | [219](../ErEpr/KMS.lean#L219) | 標準三公理 |  |  |  |

## KMSPair（11 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `KMSPair.tracial_iff_period` | [52](../ErEpr/KMSPair.lean#L52) | 標準三公理 | T1 | T1 |  |
| `KMSPair.ofComm` | [65](../ErEpr/KMSPair.lean#L65) | 標準三公理 |  |  |  |
| `gibbs_mul_inv` | [83](../ErEpr/KMSPair.lean#L83) | 標準三公理 |  |  |  |
| `gibbs_isUnit` | [89](../ErEpr/KMSPair.lean#L89) | 標準三公理 |  |  |  |
| `gibbsKMSPair_ω` | [114](../ErEpr/KMSPair.lean#L114) | 標準三公理 |  |  |  |
| `gibbsKMSPair_ν` | [117](../ErEpr/KMSPair.lean#L117) | 標準三公理 |  |  |  |
| `gibbs_tracial_iff_scalar` | [123](../ErEpr/KMSPair.lean#L123) | 標準三公理 |  |  | ⇒ KMSPair.tracial_iff_period gibbs_isKMS |
| `negctrl_diag_not_tracial` | [144](../ErEpr/KMSPair.lean#L144) | 標準三公理 |  |  |  |
| `negctrl_gibbs_not_tracial` | [161](../ErEpr/KMSPair.lean#L161) | 標準三公理 |  |  |  |
| `negctrl_nondeg_needed` | [171](../ErEpr/KMSPair.lean#L171) | 標準三公理 |  |  |  |
| `no_ringHom_matrix_to_comm` | [186](../ErEpr/KMSPair.lean#L186) | 標準三公理 |  |  |  |

## Charts（53 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `hasDerivAt_kf` | [84](../ErEpr/Charts.lean#L84) | 標準三公理 |  |  |  |
| `kf_strictMonoOn` | [95](../ErEpr/Charts.lean#L95) | 標準三公理 |  |  |  |
| `kf_two_M` | [103](../ErEpr/Charts.lean#L103) | 標準三公理 |  |  |  |
| `kf_pos_iff` | [106](../ErEpr/Charts.lean#L106) | 標準三公理 |  |  |  |
| `kf_neg_iff` | [109](../ErEpr/Charts.lean#L109) | 標準三公理 |  |  |  |
| `kf_eq_zero_iff` | [120](../ErEpr/Charts.lean#L120) | 標準三公理 |  |  |  |
| `FS_pos` | [124](../ErEpr/Charts.lean#L124) | 標準三公理 |  |  |  |
| `FK_mul_kf` | [132](../ErEpr/Charts.lean#L132) | 標準三公理 | C1 | C1 |  |
| `hasDerivAt_sqrt_kf` | [140](../ErEpr/Charts.lean#L140) | 標準三公理 |  |  |  |
| `FK_mul_dsqrtkf_sq` | [145](../ErEpr/Charts.lean#L145) | 標準三公理 |  |  |  |
| `FK_mul_deriv_sqrt_kf` | [158](../ErEpr/Charts.lean#L158) | 標準三公理 |  |  |  |
| `kruskalU_mul_V` | [172](../ErEpr/Charts.lean#L172) | 標準三公理 |  |  |  |
| `kruskalV_div_U` | [186](../ErEpr/Charts.lean#L186) | 標準三公理 |  |  |  |
| `kruskal_rightExterior` | [198](../ErEpr/Charts.lean#L198) | 標準三公理 |  |  |  |
| `kruskal_pullback` | [209](../ErEpr/Charts.lean#L209) | 標準三公理 |  | C1 |  |
| `rOfRho_eq` | [238](../ErEpr/Charts.lean#L238) | 標準三公理 |  |  |  |
| `rOfRho_pos` | [243](../ErEpr/Charts.lean#L243) | 標準三公理 |  |  |  |
| `rOfRho_throat` | [248](../ErEpr/Charts.lean#L248) | 標準三公理 |  |  |  |
| `FS_rOfRho` | [254](../ErEpr/Charts.lean#L254) | 標準三公理 |  |  |  |
| `hasDerivAt_rOfRho` | [261](../ErEpr/Charts.lean#L261) | 標準三公理 |  |  |  |
| `confIso_eq_rOfRho` | [266](../ErEpr/Charts.lean#L266) | 標準三公理 |  |  |  |
| `areaIso_eq_rOfRho` | [271](../ErEpr/Charts.lean#L271) | 標準三公理 |  |  |  |
| `iso_radial` | [276](../ErEpr/Charts.lean#L276) | 標準三公理 |  |  |  |
| `iso_angular` | [283](../ErEpr/Charts.lean#L283) | 標準三公理 |  |  |  |
| `rOfRho_inv` | [292](../ErEpr/Charts.lean#L292) | 標準三公理 |  |  |  |
| `sliceX_inv` | [299](../ErEpr/Charts.lean#L299) | 標準三公理 | C2 | C2 |  |
| `sliceX_sq` | [311](../ErEpr/Charts.lean#L311) | 標準三公理 |  |  |  |
| `sliceX_deriv_alg` | [321](../ErEpr/Charts.lean#L321) | 標準三公理 |  |  |  |
| `hasDerivAt_sliceX` | [340](../ErEpr/Charts.lean#L340) | 標準三公理 |  |  |  |
| `FK_mul_deriv_sliceX_sq` | [357](../ErEpr/Charts.lean#L357) | 標準三公理 |  |  |  |
| `sliceX_throat` | [369](../ErEpr/Charts.lean#L369) | 標準三公理 |  |  |  |
| `slice_rightExterior` | [373](../ErEpr/Charts.lean#L373) | 標準三公理 |  |  |  |
| `slice_leftExterior` | [381](../ErEpr/Charts.lean#L381) | 標準三公理 |  |  |  |
| `slice_prod` | [389](../ErEpr/Charts.lean#L389) | 標準三公理 |  |  |  |
| `inversion_swaps_UV` | [394](../ErEpr/Charts.lean#L394) | 標準三公理 |  | C2 | ⇒ sliceX_inv |
| `boost_preserves_prod` | [401](../ErEpr/Charts.lean#L401) | 標準三公理 | C3 | C3 |  |
| `boost_metric` | [406](../ErEpr/Charts.lean#L406) | 標準三公理 |  | C3 |  |
| `exp_mul_pos_iff` | [410](../ErEpr/Charts.lean#L410) | 標準三公理 |  |  |  |
| `exp_mul_neg_iff` | [413](../ErEpr/Charts.lean#L413) | 標準三公理 |  |  |  |
| `futureCausal_boost_of` | [420](../ErEpr/Charts.lean#L420) | 標準三公理 |  | C3 |  |
| `futureCausal_boost` | [439](../ErEpr/Charts.lean#L439) | 標準三公理 |  |  |  |
| `rightExterior_boost` | [450](../ErEpr/Charts.lean#L450) | 標準三公理 |  |  |  |
| `leftExterior_boost` | [455](../ErEpr/Charts.lean#L455) | 標準三公理 |  |  |  |
| `futureInterior_boost` | [460](../ErEpr/Charts.lean#L460) | 標準三公理 |  |  |  |
| `negctrl_boost_spacelike` | [467](../ErEpr/Charts.lean#L467) | 標準三公理 |  |  |  |
| `r_gt_of_slice` | [482](../ErEpr/Charts.lean#L482) | 標準三公理 |  |  |  |
| `r_lt_of_timelike` | [489](../ErEpr/Charts.lean#L489) | 標準三公理 |  |  |  |
| `r_eq_at_bifurcation` | [496](../ErEpr/Charts.lean#L496) | 標準三公理 |  |  |  |
| `area_lt_area_iff` | [502](../ErEpr/Charts.lean#L502) | 標準三公理 |  |  |  |
| `area_slice_gt` | [517](../ErEpr/Charts.lean#L517) | 標準三公理 |  |  |  |
| `area_timelike_lt` | [525](../ErEpr/Charts.lean#L525) | 標準三公理 |  |  |  |
| `area_bifurcation_eq` | [533](../ErEpr/Charts.lean#L533) | 標準三公理 |  |  |  |
| `negctrl_interior_area` | [541](../ErEpr/Charts.lean#L541) | 標準三公理 |  |  |  |

## MinCut（31 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `card_cutEdges_eq_sum` | [62](../ErEpr/MinCut.lean#L62) | 標準三公理 |  |  |  |
| `cutInd_submod` | [71](../ErEpr/MinCut.lean#L71) | 零公理 |  |  |  |
| `cutEdges_card_submodular` | [76](../ErEpr/MinCut.lean#L76) | 標準三公理 | M1 | M1 |  |
| `cutEdges_compl` | [86](../ErEpr/MinCut.lean#L86) | 標準三公理 |  |  |  |
| `minCut_le` | [100](../ErEpr/MinCut.lean#L100) | 標準三公理 |  |  |  |
| `exists_minCut` | [105](../ErEpr/MinCut.lean#L105) | 標準三公理 |  |  |  |
| `mmi_contract` | [119](../ErEpr/MinCut.lean#L119) | 零公理 |  |  |  |
| `mmi_boundary` | [126](../ErEpr/MinCut.lean#L126) | 零公理 |  |  |  |
| `decide_mem_contractSet` | [138](../ErEpr/MinCut.lean#L138) | 標準三公理 |  |  |  |
| `contractSet_inter` | [143](../ErEpr/MinCut.lean#L143) | 標準三公理 |  |  |  |
| `decide_mem_of_inter` | [154](../ErEpr/MinCut.lean#L154) | 標準三公理 |  |  |  |
| `decide_and_eq_false_of_disjoint` | [160](../ErEpr/MinCut.lean#L160) | 標準三公理 |  |  |  |
| `minCut_mmi` | [167](../ErEpr/MinCut.lean#L167) | 標準三公理 | M2b | M2b |  |
| `regionState_eq_ptrB_reindex` | [234](../ErEpr/MinCut.lean#L234) | 標準三公理 |  |  |  |
| `vnEntropy_reindex` | [244](../ErEpr/MinCut.lean#L244) | 標準三公理 |  |  |  |
| `merge_eq_const` | [254](../ErEpr/MinCut.lean#L254) | 標準三公理 |  |  |  |
| `cutMat_ghz` | [269](../ErEpr/MinCut.lean#L269) | 標準三公理 |  |  |  |
| `sBell_mul_star` | [276](../ErEpr/MinCut.lean#L276) | 標準三公理 |  |  |  |
| `two_point_entry` | [281](../ErEpr/MinCut.lean#L281) | 標準三公理 |  |  |  |
| `regionState_ghz` | [308](../ErEpr/MinCut.lean#L308) | 標準三公理 |  |  |  |
| `negMulLog_sum_two` | [335](../ErEpr/MinCut.lean#L335) | 標準三公理 |  |  |  |
| `regionEntropy_ghz` | [342](../ErEpr/MinCut.lean#L342) | 標準三公理 |  |  |  |
| `trace_regionState_ghz` | [352](../ErEpr/MinCut.lean#L352) | 標準三公理 |  |  |  |
| `ghz4_mmi_fails` | [367](../ErEpr/MinCut.lean#L367) | 標準三公理 |  |  | ⇒ regionEntropy_ghz |
| `ghz4_not_minCut` | [385](../ErEpr/MinCut.lean#L385) | 標準三公理 |  | M2b | ⇒ minCut_mmi regionEntropy_ghz mmi_contract；⇏ ghz4_mmi_fails |
| `rank_le_one_iff_vecMulVec` | [421](../ErEpr/MinCut.lean#L421) | 標準三公理 | G2 | G2 |  |
| `tnAmp_product_of_no_cut` | [443](../ErEpr/MinCut.lean#L443) | 標準三公理 |  | G2 |  |
| `tnAmp_rankOne` | [461](../ErEpr/MinCut.lean#L461) | 標準三公理 |  |  |  |
| `rank_cutMat_rankOne_le` | [469](../ErEpr/MinCut.lean#L469) | 標準三公理 |  | G2 |  |
| `rank_cutMat_eq_of_inj_surj` | [493](../ErEpr/MinCut.lean#L493) | 標準三公理 |  |  |  |
| `negctrl_product_with_bond` | [508](../ErEpr/MinCut.lean#L508) | 標準三公理 |  |  |  |

## Triangle（10 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `bekensteinBound_throat` | [46](../ErEpr/Triangle.lean#L46) | 標準三公理 | TA1 | TA1 |  |
| `first_law_saturates_bekenstein` | [52](../ErEpr/Triangle.lean#L52) | 標準三公理 |  |  | ⇒ first_law_area rOfRho_throat throat_area_eq；⇏ vnEntropy_le_beta_energy_add_log klein_gap_eq |
| `negctrl_bekenstein_isotropic_radius` | [60](../ErEpr/Triangle.lean#L60) | 標準三公理 |  |  |  |
| `reservoir_entropy_le_beta_heat` | [72](../ErEpr/Triangle.lean#L72) | 標準三公理 | TB1、TB2 | TB1、TB2 | ⇒ ；⇏ hawking_beta first_law_area |
| `reservoir_entropy_eq_beta_heat_iff` | [82](../ErEpr/Triangle.lean#L82) | 標準三公理 |  |  |  |
| `landauer_reservoir_bit` | [92](../ErEpr/Triangle.lean#L92) | 標準三公理 |  | TB1、TB2 |  |
| `negctrl_reservoir_not_gibbs` | [103](../ErEpr/Triangle.lean#L103) | 標準三公理 |  |  |  |
| `bh_energy_of_entropy` | [122](../ErEpr/Triangle.lean#L122) | 標準三公理 |  |  |  |
| `hasDerivAt_bh_energy_of_entropy` | [127](../ErEpr/Triangle.lean#L127) | 標準三公理 | TE1 | TE1 |  |
| `bh_landauer_saturated` | [143](../ErEpr/Triangle.lean#L143) | 標準三公理 |  | TE1 | ⇒ hawking_beta hasDerivAt_bh_energy_of_entropy；⇏ vnEntropy_le_beta_energy_add_log klein_gap_eq |

## Modular（13 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `modHamOf_isHermitian` | [46](../ErEpr/Modular.lean#L46) | 標準三公理 |  | TC1 |  |
| `exp_neg_modHamOf` | [54](../ErEpr/Modular.lean#L54) | 標準三公理 | TC1 | TC1 |  |
| `trace_unitary_conj_diag` | [72](../ErEpr/Modular.lean#L72) | 標準三公理 |  |  |  |
| `gibbs_modHamOf` | [78](../ErEpr/Modular.lean#L78) | 標準三公理 |  |  |  |
| `partZ_modHamOf` | [85](../ErEpr/Modular.lean#L85) | 標準三公理 |  |  |  |
| `modHamOf_gibbs` | [93](../ErEpr/Modular.lean#L93) | 標準三公理 |  | TC1 | ⇒ eigU_spectral |
| `entropy_le_modular` | [118](../ErEpr/Modular.lean#L118) | 標準三公理 | TC2 | TC2 | ⇒ ；⇏ hawking_beta first_law_area |
| `entropy_eq_modular_iff` | [130](../ErEpr/Modular.lean#L130) | 標準三公理 |  |  |  |
| `relEntropyOf_nonneg` | [148](../ErEpr/Modular.lean#L148) | 標準三公理 |  |  | ⇒ vnEntropy_le_beta_energy_add_log partZ_modHamOf |
| `relEntropyOf_eq_zero_iff` | [157](../ErEpr/Modular.lean#L157) | 標準三公理 |  |  |  |
| `relEntropyOf_diagonal` | [170](../ErEpr/Modular.lean#L170) | 標準三公理 | TC1、TC3 | TC1、TC3 |  |
| `entropy_le_modHam` | [188](../ErEpr/Modular.lean#L188) | 標準三公理 |  | TC2 |  |
| `negctrl_modular_not_fullRank` | [199](../ErEpr/Modular.lean#L199) | 標準三公理 |  |  |  |

## FirstLaw（11 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `vnEntropy_diagPath` | [43](../ErEpr/FirstLaw.lean#L43) | 標準三公理 |  |  |  |
| `modEnergy_diagPath` | [48](../ErEpr/FirstLaw.lean#L48) | 標準三公理 |  |  |  |
| `trace_diagPath` | [54](../ErEpr/FirstLaw.lean#L54) | 標準三公理 |  |  |  |
| `diagPath_posSemidef` | [60](../ErEpr/FirstLaw.lean#L60) | 標準三公理 |  |  |  |
| `hasDerivAt_entropy_diagPath` | [67](../ErEpr/FirstLaw.lean#L67) | 標準三公理 |  |  |  |
| `hasDerivAt_modEnergy_diagPath` | [82](../ErEpr/FirstLaw.lean#L82) | 標準三公理 |  |  |  |
| `entanglement_first_law_diag` | [92](../ErEpr/FirstLaw.lean#L92) | 標準三公理 | FL1 | FL1 | ⇒ hasDerivAt_entropy_diagPath hasDerivAt_modEnergy_diagPath；⇏ relEntropyOf_nonneg vnEntropy_le_beta_energy_add_log |
| `eventually_diagPath_pos` | [106](../ErEpr/FirstLaw.lean#L106) | 標準三公理 |  |  |  |
| `first_law_of_relEntropy_min` | [116](../ErEpr/FirstLaw.lean#L116) | 標準三公理 | FL2 | FL2 | ⇒ relEntropyOf_nonneg relEntropyOf_diagonal；⇏  |
| `relEntropy_diagPath_pos` | [140](../ErEpr/FirstLaw.lean#L140) | 標準三公理 |  |  | ⇒ relEntropyOf_eq_zero_iff |
| `negctrl_first_law_wrong_reference` | [167](../ErEpr/FirstLaw.lean#L167) | 標準三公理 | FL3 | FL3 |  |

## FirstLawGeneral（20 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `kleinGap_le_sq` | [43](../ErEpr/FirstLawGeneral.lean#L43) | 標準三公理 | FG1 | FG1 |  |
| `sum_sq_doubly_stochastic` | [62](../ErEpr/FirstLawGeneral.lean#L62) | 標準三公理 |  |  |  |
| `trace_mul_self_eq_sum` | [89](../ErEpr/FirstLawGeneral.lean#L89) | 標準三公理 |  |  |  |
| `trace_gibbs_mul_self_eq_sum` | [99](../ErEpr/FirstLawGeneral.lean#L99) | 標準三公理 |  |  |  |
| `trace_mul_gibbs_eq_sum` | [108](../ErEpr/FirstLawGeneral.lean#L108) | 標準三公理 |  |  |  |
| `trace_sub_gibbs_sq_eq_sum` | [127](../ErEpr/FirstLawGeneral.lean#L127) | 標準三公理 |  |  |  |
| `klein_gap_le_sq` | [145](../ErEpr/FirstLawGeneral.lean#L145) | 標準三公理 |  | FG1 |  |
| `exists_gibbs_lower` | [164](../ErEpr/FirstLawGeneral.lean#L164) | 標準三公理 |  |  |  |
| `trace_gibbsPath` | [178](../ErEpr/FirstLawGeneral.lean#L178) | 標準三公理 |  |  |  |
| `gibbsPath_zero` | [182](../ErEpr/FirstLawGeneral.lean#L182) | 標準三公理 |  |  |  |
| `energy_gibbsPath` | [187](../ErEpr/FirstLawGeneral.lean#L187) | 標準三公理 |  |  |  |
| `sq_gibbsPath` | [194](../ErEpr/FirstLawGeneral.lean#L194) | 標準三公理 |  |  |  |
| `gibbs_sub_smul_one_posSemidef` | [201](../ErEpr/FirstLawGeneral.lean#L201) | 標準三公理 |  |  |  |
| `eventually_smul_one_add_posSemidef` | [219](../ErEpr/FirstLawGeneral.lean#L219) | 標準三公理 |  |  |  |
| `eventually_gibbsPath_posSemidef` | [243](../ErEpr/FirstLawGeneral.lean#L243) | 標準三公理 |  |  |  |
| `hasDerivAt_entropy_gibbsPath` | [257](../ErEpr/FirstLawGeneral.lean#L257) | 標準三公理 | FG2、FG3 | FG2、FG3 | ⇒ ；⇏  |
| `first_law_gibbs_of_hasDerivAt` | [286](../ErEpr/FirstLawGeneral.lean#L286) | 標準三公理 |  |  | ⇏ klein_gap_le_sq hasDerivAt_entropy_gibbsPath |
| `entanglement_first_law` | [312](../ErEpr/FirstLawGeneral.lean#L312) | 標準三公理 |  | FG2、FG3 | ⇒ hasDerivAt_entropy_gibbsPath gibbs_modHamOf；⇏ hawking_beta first_law_area |
| `first_law_general_agrees_diag` | [331](../ErEpr/FirstLawGeneral.lean#L331) | 標準三公理 |  |  | ⇒ entanglement_first_law hasDerivAt_entropy_diagPath |
| `negctrl_first_law_not_fullRank` | [361](../ErEpr/FirstLawGeneral.lean#L361) | 標準三公理 | FG4 | FG4 |  |

## GammaRotation（6 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `norm_gammaKernel` | [28](../ErEpr/GammaRotation.lean#L28) | 標準三公理 |  |  |  |
| `continuousOn_gammaKernel` | [33](../ErEpr/GammaRotation.lean#L33) | 標準三公理 |  |  |  |
| `integrableOn_gammaKernel` | [40](../ErEpr/GammaRotation.lean#L40) | 標準三公理 |  |  |  |
| `hasDerivAt_gammaKernel` | [48](../ErEpr/GammaRotation.lean#L48) | 標準三公理 |  |  |  |
| `differentiableAt_gammaIntegral` | [57](../ErEpr/GammaRotation.lean#L57) | 標準三公理 |  |  |  |
| `integral_gammaKernel` | [101](../ErEpr/GammaRotation.lean#L101) | 標準三公理 | U6 | U6 | ⇒ differentiableAt_gammaIntegral integrableOn_gammaKernel |

## Unruh（11 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `meanOccupation_eq` | [47](../ErEpr/Unruh.lean#L47) | 標準三公理 | U1 | U1 | ⇏ integral_gammaKernel bogoliubov_ratio_regularized |
| `bogoliubov_thermal` | [68](../ErEpr/Unruh.lean#L68) | 標準三公理 | U2 | U1、U2 |  |
| `negctrl_bogoliubov_fermi` | [88](../ErEpr/Unruh.lean#L88) | 標準三公理 |  | U1 |  |
| `hasDerivAt_FS_horizon` | [109](../ErEpr/Unruh.lean#L109) | 標準三公理 | U3 | U3 | ⇏ hawking_beta conicalRatio_tendsto |
| `surfaceGravity_schwarzschild` | [123](../ErEpr/Unruh.lean#L123) | 標準三公理 |  | U3 |  |
| `unitConeAngle_of_surfaceGravity` | [129](../ErEpr/Unruh.lean#L129) | 標準三公理 |  |  | ⇒ hawking_beta surfaceGravity_schwarzschild |
| `bogoliubov_ratio_regularized` | [140](../ErEpr/Unruh.lean#L140) | 標準三公理 |  |  | ⇏ hawking_beta first_law_area |
| `bogoliubov_ratio_tendsto` | [194](../ErEpr/Unruh.lean#L194) | 標準三公理 | U4 | U4 |  |
| `bogoliubov_ratio_sq_tendsto` | [214](../ErEpr/Unruh.lean#L214) | 標準三公理 |  | U4 | ⇒  |
| `bogoliubov_factor_schwarzschild` | [229](../ErEpr/Unruh.lean#L229) | 標準三公理 |  |  |  |
| `negctrl_no_horizon` | [237](../ErEpr/Unruh.lean#L237) | 標準三公理 | U5 | U5 |  |

## Landauer（36 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `trace_ptrA_mul` | [57](../ErEpr/Landauer.lean#L57) | 標準三公理 |  |  |  |
| `ptrA_kronecker` | [74](../ErEpr/Landauer.lean#L74) | 標準三公理 |  |  |  |
| `trace_ptrA` | [82](../ErEpr/Landauer.lean#L82) | 標準三公理 |  |  |  |
| `ptrA_posSemidef` | [88](../ErEpr/Landauer.lean#L88) | 標準三公理 |  |  |  |
| `star_kronecker` | [94](../ErEpr/Landauer.lean#L94) | 標準三公理 |  |  |  |
| `kronecker_star_mul` | [97](../ErEpr/Landauer.lean#L97) | 標準三公理 |  |  |  |
| `kronecker_mul_star` | [101](../ErEpr/Landauer.lean#L101) | 標準三公理 |  |  |  |
| `coe_kronU` | [113](../ErEpr/Landauer.lean#L113) | 標準三公理 |  |  |  |
| `kronecker_spectral` | [119](../ErEpr/Landauer.lean#L119) | 標準三公理 |  |  |  |
| `vnEntropy_kronecker` | [134](../ErEpr/Landauer.lean#L134) | 標準三公理 |  |  | ⇏ vnEntropy_le_beta_energy_add_log klein_gap_eq |
| `modHamOf_kronecker` | [147](../ErEpr/Landauer.lean#L147) | 標準三公理 |  |  |  |
| `trace_mul_modHamOf_of_eq` | [166](../ErEpr/Landauer.lean#L166) | 標準三公理 |  |  |  |
| `vnEntropy_le_marginal_cross` | [182](../ErEpr/Landauer.lean#L182) | 標準三公理 |  |  |  |
| `mixUnif_pos` | [204](../ErEpr/Landauer.lean#L204) | 標準三公理 | LD4 | LD4 |  |
| `sum_mixUnif` | [213](../ErEpr/Landauer.lean#L213) | 標準三公理 |  | LD4 |  |
| `tendsto_mul_log_mixUnif` | [223](../ErEpr/Landauer.lean#L223) | 標準三公理 |  |  |  |
| `vnEntropy_le_of_marginal_spectral` | [238](../ErEpr/Landauer.lean#L238) | 標準三公理 |  | LD4 |  |
| `vnEntropy_subadditive` | [278](../ErEpr/Landauer.lean#L278) | 標準三公理 | LD1 | LD1 | ⇒ ；⇏ reservoir_entropy_le_beta_heat entropy_le_modular |
| `landauer` | [293](../ErEpr/Landauer.lean#L293) | 標準三公理 | LD2、LD3 | LD1、LD2、LD3 | ⇒ ；⇏ hawking_beta first_law_area |
| `landauer_bit` | [314](../ErEpr/Landauer.lean#L314) | 標準三公理 |  | LD2、LD3 |  |
| `no_heatless_erasure` | [325](../ErEpr/Landauer.lean#L325) | 標準三公理 |  | LD2、LD3 |  |
| `swapU_mul_apply` | [345](../ErEpr/Landauer.lean#L345) | 標準三公理 |  |  |  |
| `mul_swapU_apply` | [349](../ErEpr/Landauer.lean#L349) | 標準三公理 |  |  |  |
| `star_swapU` | [354](../ErEpr/Landauer.lean#L354) | 標準三公理 |  |  |  |
| `swapU_star_mul` | [364](../ErEpr/Landauer.lean#L364) | 標準三公理 |  |  |  |
| `swapU_conj_kronecker` | [371](../ErEpr/Landauer.lean#L371) | 標準三公理 |  |  |  |
| `mix2_posSemidef` | [383](../ErEpr/Landauer.lean#L383) | 標準三公理 |  |  |  |
| `trace_mix2` | [386](../ErEpr/Landauer.lean#L386) | 標準三公理 |  |  |  |
| `vnEntropy_mix2` | [390](../ErEpr/Landauer.lean#L390) | 標準三公理 |  |  |  |
| `vnEntropy_ket0Proj` | [395](../ErEpr/Landauer.lean#L395) | 標準三公理 |  |  |  |
| `vnEntropy_gibbs_H2_log2_lt` | [400](../ErEpr/Landauer.lean#L400) | 標準三公理 |  |  |  |
| `landauer_swap_witness` | [415](../ErEpr/Landauer.lean#L415) | 標準三公理 |  |  | ⇒ swapU_conj_kronecker vnEntropy_gibbs_H2_log2_lt |
| `resetS_not_unitary` | [432](../ErEpr/Landauer.lean#L432) | 標準三公理 |  |  |  |
| `resetS_conj_mix2` | [437](../ErEpr/Landauer.lean#L437) | 標準三公理 |  |  |  |
| `negctrl_landauer_not_unitary` | [444](../ErEpr/Landauer.lean#L444) | 標準三公理 |  |  | ⇒ resetS_conj_mix2 ptrA_kronecker |
| `negctrl_subadditive_unnormalized` | [459](../ErEpr/Landauer.lean#L459) | 標準三公理 |  |  |  |

## Correlated（24 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `star_bellK` | [46](../ErEpr/Correlated.lean#L46) | 標準三公理 |  |  |  |
| `bellK_mul_self` | [51](../ErEpr/Correlated.lean#L51) | 標準三公理 | BL1 | BL1 |  |
| `bellK_conj_maxEnt` | [57](../ErEpr/Correlated.lean#L57) | 標準三公理 | BL1 | BL1 |  |
| `sBell_mul_self_complex` | [64](../ErEpr/Correlated.lean#L64) | 標準三公理 |  |  |  |
| `star_disentangle` | [71](../ErEpr/Correlated.lean#L71) | 標準三公理 |  |  |  |
| `disentangle_mul_self` | [74](../ErEpr/Correlated.lean#L74) | 標準三公理 |  |  |  |
| `disentangle_star_mul` | [80](../ErEpr/Correlated.lean#L80) | 標準三公理 |  |  |  |
| `disentangle_conj_maxEnt` | [84](../ErEpr/Correlated.lean#L84) | 標準三公理 |  |  |  |
| `maxEnt_eq_disentangle_conj` | [91](../ErEpr/Correlated.lean#L91) | 標準三公理 |  |  |  |
| `vnEntropy_bell` | [100](../ErEpr/Correlated.lean#L100) | 標準三公理 |  |  | ⇒ disentangle_conj_maxEnt vnEntropy_kronecker vnEntropy_unitary_conj；⇏ vnEntropy_le_log_rank |
| `vnEntropy_ptrB_bell` | [105](../ErEpr/Correlated.lean#L105) | 標準三公理 |  |  |  |
| `vnEntropy_ptrA_bell` | [108](../ErEpr/Correlated.lean#L108) | 標準三公理 |  |  |  |
| `bell_conditional_entropy` | [112](../ErEpr/Correlated.lean#L112) | 標準三公理 |  |  |  |
| `bell_mutual_information` | [117](../ErEpr/Correlated.lean#L117) | 標準三公理 |  |  |  |
| `negctrl_entropy_monotone` | [124](../ErEpr/Correlated.lean#L124) | 標準三公理 |  |  |  |
| `negMulLog_sum_le` | [132](../ErEpr/Correlated.lean#L132) | 標準三公理 |  |  |  |
| `vnEntropy_ptrB_diagonal_le` | [151](../ErEpr/Correlated.lean#L151) | 標準三公理 | BL3 | BL3 | ⇏ vnEntropy_subadditive disentangle_conj_maxEnt |
| `gibbs_zero_ham` | [166](../ErEpr/Correlated.lean#L166) | 標準三公理 |  |  |  |
| `product_start_no_erasure` | [173](../ErEpr/Correlated.lean#L173) | 標準三公理 |  |  |  |
| `ptrA_bell_eq_gibbs` | [180](../ErEpr/Correlated.lean#L180) | 標準三公理 |  |  |  |
| `ptrB_bell_eq_mix2` | [187](../ErEpr/Correlated.lean#L187) | 標準三公理 |  |  |  |
| `ptrB_disentangle_bell` | [193](../ErEpr/Correlated.lean#L193) | 標準三公理 |  |  |  |
| `correlation_is_fuel` | [200](../ErEpr/Correlated.lean#L200) | 標準三公理 | BL2 | BL2 | ⇒ product_start_no_erasure landauer disentangle_conj_maxEnt |
| `negctrl_landauer_correlated` | [217](../ErEpr/Correlated.lean#L217) | 標準三公理 |  |  | ⇒ disentangle_conj_maxEnt ptrA_bell_eq_gibbs；⇏ landauer vnEntropy_subadditive |

## Measurement（19 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `plusProj_isHermitian` | [46](../ErEpr/Measurement.lean#L46) | 標準三公理 |  |  |  |
| `plusProj_mul_self` | [50](../ErEpr/Measurement.lean#L50) | 標準三公理 |  |  |  |
| `plusProj_posSemidef` | [54](../ErEpr/Measurement.lean#L54) | 標準三公理 |  |  |  |
| `trace_plusProj` | [60](../ErEpr/Measurement.lean#L60) | 標準三公理 |  |  |  |
| `vnEntropy_plusProj` | [66](../ErEpr/Measurement.lean#L66) | 標準三公理 |  |  | ⇏ vnEntropy_bell disentangle_conj_maxEnt |
| `star_cnot` | [84](../ErEpr/Measurement.lean#L84) | 標準三公理 |  |  |  |
| `cnot_mul_self` | [89](../ErEpr/Measurement.lean#L89) | 標準三公理 |  |  |  |
| `cnot_star_mul` | [95](../ErEpr/Measurement.lean#L95) | 標準三公理 |  |  |  |
| `cnot_measure` | [99](../ErEpr/Measurement.lean#L99) | 標準三公理 | MS1 | MS1 |  |
| `ptrB_before` | [106](../ErEpr/Measurement.lean#L106) | 標準三公理 |  |  |  |
| `ptrB_after` | [109](../ErEpr/Measurement.lean#L109) | 標準三公理 |  |  |  |
| `measurement_dephases` | [115](../ErEpr/Measurement.lean#L115) | 標準三公理 |  |  |  |
| `measurement_entropy` | [125](../ErEpr/Measurement.lean#L125) | 標準三公理 |  |  | ⇒ vnEntropy_bell vnEntropy_plusProj vnEntropy_kronecker |
| `measurement_total_entropy_conserved` | [138](../ErEpr/Measurement.lean#L138) | 標準三公理 |  |  |  |
| `ptrB_local_conj` | [145](../ErEpr/Measurement.lean#L145) | 標準三公理 | LOC1 | LOC1 |  |
| `local_cannot_undo` | [158](../ErEpr/Measurement.lean#L158) | 標準三公理 | MS2 | LOC1、MS2 | ⇒ ptrB_local_conj vnEntropy_unitary_conj cnot_measure；⇏ Kraus.no_signalling |
| `pointer_cannot_undo` | [165](../ErEpr/Measurement.lean#L165) | 標準三公理 | MS3 | MS3 | ⇒ Kraus.no_signalling cnot_measure；⇏ ptrB_local_conj |
| `joint_undo` | [171](../ErEpr/Measurement.lean#L171) | 標準三公理 |  |  | ⇒ disentangle_conj_maxEnt cnot_mul_self |
| `negctrl_local_no_decoherence` | [187](../ErEpr/Measurement.lean#L187) | 標準三公理 |  | LOC1 |  |

## Monogamy（16 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `exists_eq_conjTranspose_mul_self` | [44](../ErEpr/Monogamy.lean#L44) | 標準三公理 |  |  |  |
| `mul_eq_zero_of_trace_mul_eq_zero` | [61](../ErEpr/Monogamy.lean#L61) | 標準三公理 |  |  |  |
| `rankOne_mul_self` | [74](../ErEpr/Monogamy.lean#L74) | 標準三公理 |  |  |  |
| `rankOne_conjTranspose` | [85](../ErEpr/Monogamy.lean#L85) | 標準三公理 |  |  |  |
| `trace_rankOne` | [93](../ErEpr/Monogamy.lean#L93) | 標準三公理 |  |  |  |
| `rankOne_kron_one_conj` | [102](../ErEpr/Monogamy.lean#L102) | 標準三公理 | MG3 | MG3 |  |
| `monogamy` | [116](../ErEpr/Monogamy.lean#L116) | 標準三公理 | MG1 | MG1、MG3 | ⇒ mul_eq_zero_of_trace_mul_eq_zero rankOne_kron_one_conj trace_ptrB_mul；⇏ vnEntropy_le_beta_energy_add_log relEntropyOf_nonneg |
| `ptrMid_kronecker` | [175](../ErEpr/Monogamy.lean#L175) | 標準三公理 |  |  |  |
| `ptrMid_kronecker3` | [182](../ErEpr/Monogamy.lean#L182) | 標準三公理 |  |  |  |
| `monogamy_mutualInfo` | [187](../ErEpr/Monogamy.lean#L187) | 標準三公理 |  | MG1 | ⇒ monogamy ptrMid_kronecker vnEntropy_kronecker |
| `maxEnt_posSemidef` | [208](../ErEpr/Monogamy.lean#L208) | 標準三公理 |  |  |  |
| `trace_maxEnt` | [212](../ErEpr/Monogamy.lean#L212) | 標準三公理 |  |  |  |
| `bell_rankOne_norm` | [216](../ErEpr/Monogamy.lean#L216) | 標準三公理 |  |  |  |
| `bell_monogamy` | [223](../ErEpr/Monogamy.lean#L223) | 標準三公理 | MG2 | MG1、MG2 | ⇒ monogamy_mutualInfo bell_mutual_information |
| `bell_monogamy_witness` | [240](../ErEpr/Monogamy.lean#L240) | 標準三公理 |  |  |  |
| `negctrl_monogamy_mixed` | [247](../ErEpr/Monogamy.lean#L247) | 標準三公理 |  |  | ⇏ monogamy mul_eq_zero_of_trace_mul_eq_zero |

## Swapping（50 條）

| 定理 | 行 | 公理 | 演習（必須紅） | 演習（實際紅） | 耦合斷言 |
|---|---|---|---|---|---|
| `mutualInfo_kronecker` | [49](../ErEpr/Swapping.lean#L49) | 標準三公理 |  |  |  |
| `ptrBC_kronecker` | [62](../ErEpr/Swapping.lean#L62) | 標準三公理 |  |  |  |
| `ptrBC_smul` | [70](../ErEpr/Swapping.lean#L70) | 標準三公理 |  |  |  |
| `trace_ptrBC` | [77](../ErEpr/Swapping.lean#L77) | 標準三公理 |  |  |  |
| `vecMulVec_kronecker` | [86](../ErEpr/Swapping.lean#L86) | 標準三公理 |  |  |  |
| `bellPair_eq` | [103](../ErEpr/Swapping.lean#L103) | 標準三公理 |  |  |  |
| `fin_two_one_add_one` | [113](../ErEpr/Swapping.lean#L113) | 標準公理子集（propext） |  |  |  |
| `swapProj_mulVec` | [132](../ErEpr/Swapping.lean#L132) | 標準三公理 | SW1 | SW1 |  |
| `vecMul_swapProj` | [139](../ErEpr/Swapping.lean#L139) | 標準三公理 |  | SW1 |  |
| `swap_post` | [147](../ErEpr/Swapping.lean#L147) | 標準三公理 |  |  |  |
| `star_swapVec` | [159](../ErEpr/Swapping.lean#L159) | 標準三公理 |  |  |  |
| `ptrBC_swapVec_00` | [165](../ErEpr/Swapping.lean#L165) | 標準三公理 |  |  |  |
| `ptrBC_swapVec_01` | [170](../ErEpr/Swapping.lean#L170) | 標準三公理 |  |  |  |
| `ptrBC_swapVec_10` | [175](../ErEpr/Swapping.lean#L175) | 標準三公理 |  |  |  |
| `ptrBC_swapVec_11` | [180](../ErEpr/Swapping.lean#L180) | 標準三公理 |  |  |  |
| `ptrBC_swapVec` | [185](../ErEpr/Swapping.lean#L185) | 標準三公理 |  |  |  |
| `trace_bellAD` | [194](../ErEpr/Swapping.lean#L194) | 標準三公理 |  |  |  |
| `bellAD_zero` | [198](../ErEpr/Swapping.lean#L198) | 標準三公理 |  |  |  |
| `ptrBC_swap_post` | [204](../ErEpr/Swapping.lean#L204) | 標準三公理 |  |  |  |
| `swap_prob` | [210](../ErEpr/Swapping.lean#L210) | 標準三公理 |  |  |  |
| `swap_before` | [217](../ErEpr/Swapping.lean#L217) | 標準三公理 |  |  |  |
| `entanglement_swapping` | [228](../ErEpr/Swapping.lean#L228) | 標準三公理 | SW2 | SW2 | ⇒ swapProj_mulVec ptrBC_swap_post bell_mutual_information |
| `swap_average_eq` | [248](../ErEpr/Swapping.lean#L248) | 標準三公理 |  |  |  |
| `swap_average_no_signalling` | [258](../ErEpr/Swapping.lean#L258) | 標準三公理 | SW3 | SW3 | ⇒ swap_average_eq ptrBC_kronecker；⇏ entanglement_swapping |
| `sepProj_mulVec` | [274](../ErEpr/Swapping.lean#L274) | 標準三公理 |  |  |  |
| `vecMul_sepProj` | [281](../ErEpr/Swapping.lean#L281) | 標準三公理 |  |  |  |
| `ptrBC_sepVec` | [288](../ErEpr/Swapping.lean#L288) | 標準三公理 |  |  |  |
| `negctrl_swap_separate` | [294](../ErEpr/Swapping.lean#L294) | 標準三公理 |  |  | ⇒ sepProj_mulVec mutualInfo_kronecker；⇏ swapProj swapProj_mulVec |
| `star_bellSign` | [319](../ErEpr/Swapping.lean#L319) | 標準三公理 |  |  |  |
| `bellVecBC_norm` | [330](../ErEpr/Swapping.lean#L330) | 標準三公理 |  |  |  |
| `bellProjBC_mul_self` | [335](../ErEpr/Swapping.lean#L335) | 標準三公理 | SWP1 | SWP1 |  |
| `bellProjBC_conjTranspose` | [338](../ErEpr/Swapping.lean#L338) | 標準三公理 |  |  |  |
| `sum_bellProjBC` | [341](../ErEpr/Swapping.lean#L341) | 標準三公理 | SWP1 | SWP1 |  |
| `swapProj_eq_reindex` | [355](../ErEpr/Swapping.lean#L355) | 標準三公理 |  | SW1、SWP1 |  |
| `swapProj_isHermitian` | [367](../ErEpr/Swapping.lean#L367) | 標準三公理 |  |  |  |
| `swapProj_mul_self` | [372](../ErEpr/Swapping.lean#L372) | 標準三公理 |  |  | ⇒ swapProj_eq_reindex rankOne_mul_self；⇏ swapProj_mulVec entanglement_swapping |
| `sum_swapProj` | [377](../ErEpr/Swapping.lean#L377) | 標準三公理 |  |  | ⇒ swapProj_eq_reindex sum_bellProjBC |
| `ptrFirst_kronecker` | [393](../ErEpr/Swapping.lean#L393) | 標準三公理 |  |  |  |
| `ptrFirst_kronecker3` | [400](../ErEpr/Swapping.lean#L400) | 標準三公理 |  |  |  |
| `amps_monogamy` | [407](../ErEpr/Swapping.lean#L407) | 標準三公理 | AF1 | AF1 |  |
| `amps_contradiction` | [428](../ErEpr/Swapping.lean#L428) | 標準三公理 |  | AF1 | ⇒ amps_monogamy monogamy ptrFirst_kronecker |
| `ampsUnitaryState_posSemidef` | [445](../ErEpr/Swapping.lean#L445) | 標準三公理 |  |  |  |
| `ptrFirst_ampsUnitaryState` | [448](../ErEpr/Swapping.lean#L448) | 標準三公理 |  |  |  |
| `amps_each_half_satisfiable` | [458](../ErEpr/Swapping.lean#L458) | 標準三公理 |  |  | ⇒ bell_monogamy_witness ptrFirst_ampsUnitaryState |
| `ghzState_posSemidef` | [475](../ErEpr/Swapping.lean#L475) | 標準三公理 |  |  |  |
| `ptrFirst_ghzState` | [479](../ErEpr/Swapping.lean#L479) | 標準三公理 |  |  |  |
| `ptrB_ptrFirst_ghzState` | [485](../ErEpr/Swapping.lean#L485) | 標準三公理 |  |  |  |
| `ptrA_ptrFirst_ghzState` | [490](../ErEpr/Swapping.lean#L490) | 標準三公理 |  |  |  |
| `mutualInfo_ptrFirst_ghzState` | [495](../ErEpr/Swapping.lean#L495) | 標準三公理 |  |  |  |
| `negctrl_amps_mixed` | [503](../ErEpr/Swapping.lean#L503) | 標準三公理 |  |  | ⇏ monogamy amps_monogamy |
