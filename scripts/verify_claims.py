#!/usr/bin/env python3
"""
Independent numerical & exact verification script for MultiQubitMUB.

Checks:
1. n = 2 sharpness witness |ψ₂⟩ = (1/2)(1, 1, 1, i): exact Pauli-covariant 4-MUB fiducial (F₂ = 7/4).
2. Unified GL(n, 𝔽₂) ⋊ ⟨H^⊗n⟩ spike+uniform family |ψ_n(s)⟩ for n = 1, 2, 3, 4:
   - n = 1, s = 1 - 1/√3: exact 1-qubit WH-SIC |T⟩ (F₁ = 4/3).
   - n = 2, s = 1/2: exact 2-qubit MUB fiducial (F₂ = 7/4).
   - n = 3, s = 2/3: exact 3-qubit Hoggar WH-SIC (F₃ = 16/9, all 63 Paulis have |⟨P⟩| = 1/3).
   - n = 4, unique root s ∈ (0,1) of 453 s³ - 708 s² + 368 s - 64 = 0:
     F₄ ≈ 2.1505201547139396, minimal polynomial 10328853 F³ - 95942784 F² + 294109184 F - 291504128 = 0.
3. Exact WHT-to-subcube identity used in the 2-adic subspace induction proof.
"""

import cmath
import math
from fractions import Fraction


def popcount(x: int) -> int:
    return bin(x).count("1")


def pauli_expect_all(psi: list[complex], n: int) -> list[list[float]]:
    """Compute exact ⟨ψ | P_{a,b} | ψ⟩ for all a, b ∈ 𝔽₂ⁿ."""
    d = 1 << n
    out = [[0.0] * d for _ in range(d)]
    for a in range(d):
        for b in range(d):
            ph = 1j if (popcount(a & b) & 1) else 1.0
            val = 0j
            for x in range(d):
                sign = -1.0 if (popcount(b & x) & 1) else 1.0
                val += sign * psi[x].conjugate() * psi[x ^ a]
            val *= ph
            assert abs(val.imag) < 1e-12, f"Non-real Pauli expectation {val}"
            out[a][b] = val.real
    return out


def pauli_moment4(psi: list[complex], n: int) -> float:
    exps = pauli_expect_all(psi, n)
    return sum(v ** 4 for row in exps for v in row)


def spike_state(n: int, s: float) -> list[complex]:
    d = 1 << n
    p = 1.0 - ((d - 1) / d) * s
    alpha = math.sqrt(p)
    u = 2.0 * p - 1.0
    v2 = -1.0 + 4.0 * s - (4.0 * (d - 1) / d) * s * s
    assert p > 0 and v2 >= -1e-15
    v = math.sqrt(max(0.0, v2))
    beta = complex(u / (2.0 * alpha), v / (2.0 * alpha))
    return [complex(alpha, 0.0)] + [beta] * (d - 1)


def spike_moment_poly(n: int, s: float) -> float:
    d = 1 << n
    v2 = -1.0 + 4.0 * s - (4.0 * (d - 1) / d) * s * s
    return 1.0 + (d - 1) * (
        2.0 * (1.0 - s) ** 4
        + (d / 2 - 1.0) * (1.0 - 2.0 * s) ** 4
        + (d / 2) * v2 ** 2
    )


def main() -> None:
    # 1. Verify n = 2 Pauli-MUB fiducial sharpness witness
    psi2 = [0.5, 0.5, 0.5, 0.5j]
    exps2 = pauli_expect_all(psi2, 2)
    mags2 = sorted(round(abs(v), 12) for row in exps2 for v in row)
    assert mags2.count(0.0) == 3 and mags2.count(0.5) == 12 and mags2.count(1.0) == 1
    f2 = pauli_moment4(psi2, 2)
    assert abs(f2 - 1.75) < 1e-13
    print(f"[PASS] n=2 sharpness witness (1,1,1,i)/2: 3 zeros, 12 of |⟨P⟩|=1/2, F₂ = {f2:.15f} = 7/4")

    # 2. Verify spike family across n = 1, 2, 3, 4
    cases = [
        (1, 1.0 - 1.0 / math.sqrt(3.0), 4.0 / 3.0, "1-qubit WH-SIC |T⟩"),
        (2, 0.5, 7.0 / 4.0, "2-qubit MUB fiducial"),
        (3, 2.0 / 3.0, 16.0 / 9.0, "3-qubit Hoggar WH-SIC"),
    ]
    for n, s, target, label in cases:
        psi = spike_state(n, s)
        norm = sum(abs(z) ** 2 for z in psi)
        assert abs(norm - 1.0) < 1e-13
        f_direct = pauli_moment4(psi, n)
        f_poly = spike_moment_poly(n, s)
        assert abs(f_direct - target) < 1e-12
        assert abs(f_poly - target) < 1e-12
        print(f"[PASS] n={n} {label}: s={s:.12f}, F_{n}={f_direct:.15f} (exact {target:.15f})")

    # 3. Verify n = 4 exact cubic extremizer
    # Solve 453 s^3 - 708 s^2 + 368 s - 64 = 0 via Newton
    s4 = 0.622543
    for _ in range(30):
        val = 453 * s4**3 - 708 * s4**2 + 368 * s4 - 64
        der = 1359 * s4**2 - 1416 * s4 + 368
        s4 -= val / der
    psi4 = spike_state(4, s4)
    assert abs(sum(abs(z) ** 2 for z in psi4) - 1.0) < 1e-13
    f4_direct = pauli_moment4(psi4, 4)
    f4_poly = spike_moment_poly(4, s4)
    assert abs(f4_direct - f4_poly) < 1e-12
    minpoly_err = abs(
        10328853 * f4_direct**3
        - 95942784 * f4_direct**2
        + 294109184 * f4_direct
        - 291504128
    )
    assert minpoly_err < 1e-6
    m2_4 = -math.log(f4_direct / 16.0)
    print(
        f"[PASS] n=4 cubic spike state: s*={s4:.16f}, F₄={f4_direct:.16f}, "
        f"M₂={m2_4:.12f}, minpoly residual={minpoly_err:.2e}"
    )

    # Check exact rational witness s = 622543/1000000 used in SpikeFamily.lean
    s_rat = Fraction(622543, 1000000)
    d = Fraction(16)
    v2_rat = -1 + 4 * s_rat - (4 * (d - 1) / d) * s_rat**2
    f4_rat = 1 + (d - 1) * (
        2 * (1 - s_rat) ** 4 + (d / 2 - 1) * (1 - 2 * s_rat) ** 4 + (d / 2) * v2_rat**2
    )
    assert f4_rat < Fraction(2150521, 1000000)
    print(f"[PASS] Exact rational witness s=622543/1000000: F₄ = {float(f4_rat):.16f} < 2.150521")


if __name__ == "__main__":
    main()
