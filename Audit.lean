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
