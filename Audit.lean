import MultiQubitMUB

/-!
# Axiom Audit for Multi-Qubit Pauli-Covariant MUB & Alltop Non-Existence (`n ≥ 3`)

Verifies that every main theorem depends ONLY on the three standard Lean 4 / Mathlib axioms:
`propext`, `Classical.choice`, and `Quot.sound` (zero `sorryAx`, zero `Lean.ofReduceBool`).
-/

#print axioms MultiQubitMUB.no_alltop_f2
#print axioms MultiQubitMUB.exists_alltop_two
#print axioms MultiQubitMUB.phasePauliMoment4_gt_mub
#print axioms MultiQubitMUB.no_pauli_two_valued_odd
#print axioms MultiQubitMUB.no_pauli_mub_fiducial
#print axioms MultiQubitMUB.damski_conjecture_1
#print axioms MultiQubitMUB.exists_pauli_mub_fiducial_two
#print axioms MultiQubitMUB.pauliMoment4_spikeState
#print axioms MultiQubitMUB.hoggar_sic_three
#print axioms MultiQubitMUB.four_qubit_spike_bound
#print axioms MultiQubitMUB.pauliMoment4_ge_welch_add_universal
#print axioms MultiQubitMUB.pauliMoment4_gt_welch
#print axioms MultiQubitMUB.no_pauli_sic_all
#print axioms MultiQubitMUB.pauliMoment4_two_ge
#print axioms MultiQubitMUB.pauliMoment4_four_ge_kramers
#print axioms MultiQubitMUB.pauliMoment4_contextuality_bridge
#print axioms MultiQubitMUB.pauliMoment4_four_of_contextuality_1575
#print axioms MultiQubitMUB.pauliMoment4_two_ge_twelve_sevenths
#print axioms MultiQubitMUB.FourQubitMUB.symp_turan_unified
#print axioms MultiQubitMUB.FourQubitMUB.mainTree_valid
#print axioms MultiQubitMUB.pauliMoment4_four_gt_mub_of_contextuality_1575
#print axioms MultiQubitMUB.signCubeSum_four_le_6615
#print axioms MultiQubitMUB.pauliMoment4_four_ge_193_100
#print axioms MultiQubitMUB.pauliMoment4_four_gt_mub
#print axioms MultiQubitMUB.TwoQubitExactCert.symIdxTables_valid
#print axioms MultiQubitMUB.TwoQubitExactCert.allBlocks_valid
#print axioms MultiQubitMUB.TwoQubitExactCert.cert_matches_target
#print axioms MultiQubitMUB.pauliMoment4_two_ge_seven_fourths
#print axioms MultiQubitMUB.pauliMoment4_two_min_eq_seven_fourths
#print axioms MultiQubitMUB.frustPairs_Qminus72_ge_315
#print axioms MultiQubitMUB.frustPairs_W72_ge_1575
#print axioms MultiQubitMUB.frustPairs_Qminus72_spikeSign4
#print axioms MultiQubitMUB.cd_Qminus72_eq_315
#print axioms MultiQubitMUB.cd_W72_eq_1575
#print axioms MultiQubitMUB.signCubeSum_four_max_eq_6615
#print axioms MultiQubitMUB.GeneralContextualityLift.general_n_triangle_line_bit
#print axioms MultiQubitMUB.GeneralContextualityLift.general_n_triangle_line_homomorphism
#print axioms MultiQubitMUB.frustPairs_ge_five_seventeenths
#print axioms MultiQubitMUB.signCubeSum_le_seven_seventeenths
#print axioms MultiQubitMUB.signCubeSum_le_spectral
#print axioms MultiQubitMUB.frustPairs_ge_spectral
#print axioms MultiQubitMUB.frustPairs_ge_spectral_two_inv_sqrt
#print axioms MultiQubitMUB.ellipticSignCubeSum_le_spectral
#print axioms MultiQubitMUB.elliptic_frustPairs_ge_spectral
#print axioms MultiQubitMUB.matTr_cube_ge_of_rayleigh
#print axioms MultiQubitMUB.signCubeSum_ge_of_L1
#print axioms MultiQubitMUB.pauliMoment4_ge_of_contextuality_const
#print axioms MultiQubitMUB.avg_pauliExpect_z4Phase_eq_centralBinom
#print axioms MultiQubitMUB.centralBinom_sq_ge
#print axioms MultiQubitMUB.exists_signAssign_omega_inv_sqrt
#print axioms MultiQubitMUB.frustPairs_spikeSign_all
#print axioms MultiQubitMUB.spikeSign_frust_gap_eq
#print axioms MultiQubitMUB.spikeSign_strictly_suboptimal_asymptotic
#print axioms MultiQubitMUB.pow_two_add_one_ne_sq
#print axioms MultiQubitMUB.sqrt_pow_two_add_one_ne_rat
#print axioms MultiQubitMUB.signCubeSum_lt_spectral
#print axioms MultiQubitMUB.frustPairs_gt_spectral
#print axioms MultiQubitMUB.no_pauli_sic_via_cubic_trace
#print axioms MultiQubitMUB.pauliL1_ge_of_pauliMoment4
#print axioms MultiQubitMUB.pauliAlpha_ge_of_pauliMoment4
#print axioms MultiQubitMUB.exists_unit_state_rayleigh_ge_cube
#print axioms MultiQubitMUB.exists_unit_state_pauliL1_ge_of_signCubeSum
#print axioms MultiQubitMUB.exists_unit_state_pauliAlpha_ge_of_frustPairs
#print axioms MultiQubitMUB.qSIC_nonneg
#print axioms MultiQubitMUB.sum_qSIC_eq_one
#print axioms MultiQubitMUB.sympWHT_qSIC_eq
#print axioms MultiQubitMUB.sympWHT_qSIC_pow_nonneg
#print axioms MultiQubitMUB.qSIC_moment4_eq_welch
#print axioms MultiQubitMUB.signMat_diag_odd_int
#print axioms MultiQubitMUB.signMat_offdiag_even_re_im
#print axioms MultiQubitMUB.signMat_add_id_half_gaussInt
#print axioms MultiQubitMUB.compBasisIPR_eq_sum_Z_pauliSq
#print axioms MultiQubitMUB.compBasisIPR_eq_welch_of_flat_pauli
#print axioms MultiQubitMUB.compBasisIPR_sub_welch_sq_le
