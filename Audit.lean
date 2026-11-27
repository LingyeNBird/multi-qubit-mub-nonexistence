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
