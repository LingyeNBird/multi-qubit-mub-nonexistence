#!/usr/bin/env python3
"""
Independent numerical & exact verification script for MultiQubitMUB.

Checks:
1. n = 2 sharpness witness |ψ₂⟩ = (1/2)(1, 1, 1, i): exact Pauli-covariant 4-MUB fiducial (F₂ = 7/4)
   and 2-qubit Clifford orbit size 480 containing both |ψ₂⟩ and |ψ₂(1/2)⟩.
2. Spike-plus-uniform family |ψ_n(s)⟩ for n = 1, 2, 3, 4:
   - Verifies H^⊗n |ψ_n(s)⟩ = e^{iθ} |conj(ψ_n(s))⟩ (antiunitary symmetry) and exact Pauli 4th moments:
   - n = 1, s = 1 - 1/√3: exact 1-qubit WH-SIC |T⟩ (F₁ = 4/3).
   - n = 2, s = 1/2: exact 2-qubit MUB fiducial (F₂ = 7/4).
   - n = 3, s = 2/3: exact 3-qubit Hoggar WH-SIC (F₃ = 16/9, all 63 Paulis have |⟨P⟩| = 1/3).
   - n = 4, unique root s* ∈ (0,1) of 453 s³ - 708 s² + 368 s - 64 = 0:
     F₄ ≈ 2.1505201547139396, minimal polynomial 10328853 F³ - 95942784 F² + 294109184 F - 291504128 = 0.
3. Exact 4-qubit bent-support (16, 6, 2)-difference-set family achieving
   F₄ = 20/9 + (1/81) |∑_{x∈S} e^{4iθ_x}|².
4. Exact Q(√2, i) verification of closed-form continuous phase-state families attaining
   F₃ = 9/4, F₄ = 45/16, and F₅ = 21/8.
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


def hadamard_apply(psi: list[complex], n: int) -> list[complex]:
    d = 1 << n
    scale = 1.0 / math.sqrt(d)
    return [
        scale * sum(((-1.0 if (popcount(x & y) & 1) else 1.0) * psi[y]) for y in range(d))
        for x in range(d)
    ]


def check_antiunitary_hadamard(psi: list[complex], n: int) -> None:
    """Verify H^⊗n |ψ⟩ = e^{iθ} |conj(ψ)⟩ up to a global phase."""
    hpsi = hadamard_apply(psi, n)
    conj_psi = [z.conjugate() for z in psi]
    ov = sum(a.conjugate() * b for a, b in zip(conj_psi, hpsi))
    assert abs(abs(ov) - 1.0) < 1e-12, f"Antiunitary H^⊗n ∘ K symmetry failed: |⟨conj(ψ)|H^⊗n ψ⟩| = {abs(ov)}"


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
        check_antiunitary_hadamard(psi, n)
        f_direct = pauli_moment4(psi, n)
        f_poly = spike_moment_poly(n, s)
        assert abs(f_direct - target) < 1e-12
        assert abs(f_poly - target) < 1e-12
        print(f"[PASS] n={n} {label}: s={s:.12f}, F_{n}={f_direct:.15f} (exact {target:.15f}), (H^⊗n∘K)-symmetric")

    # 3. Verify n = 4 exact cubic extremizer
    # Solve 453 s^3 - 708 s^2 + 368 s - 64 = 0 via Newton
    s4 = 0.622543
    for _ in range(30):
        val = 453 * s4**3 - 708 * s4**2 + 368 * s4 - 64
        der = 1359 * s4**2 - 1416 * s4 + 368
        s4 -= val / der
    psi4 = spike_state(4, s4)
    assert abs(sum(abs(z) ** 2 for z in psi4) - 1.0) < 1e-13
    check_antiunitary_hadamard(psi4, 4)
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

    # 4. Verify 2-qubit Clifford orbit size 480 and equivalence of |ψ₂⟩ and |ψ₂(1/2)⟩
    def kron(A, B):
        ra, ca = len(A), len(A[0])
        rb, cb = len(B), len(B[0])
        return [[A[i // rb][j // cb] * B[i % rb][j % cb] for j in range(ca * cb)] for i in range(ra * rb)]

    def mv(A, v):
        return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]

    def canon_ray(v):
        for z in v:
            if abs(z) > 1e-6:
                ph = z.conjugate() / abs(z)
                v = [x * ph for x in v]
                break
        return tuple((round(x.real, 5), round(x.imag, 5)) for x in v)

    I2 = [[1, 0], [0, 1]]
    H1 = [[1 / math.sqrt(2), 1 / math.sqrt(2)], [1 / math.sqrt(2), -1 / math.sqrt(2)]]
    S1 = [[1, 0], [0, 1j]]
    CZ = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]]
    gens = [kron(H1, I2), kron(I2, H1), kron(S1, I2), kron(I2, S1), CZ]
    seen = {canon_ray(psi2): psi2}
    queue = [psi2]
    while queue:
        v = queue.pop()
        for G in gens:
            w = mv(G, v)
            key = canon_ray(w)
            if key not in seen:
                seen[key] = w
                queue.append(w)
    psi2_spike = spike_state(2, 0.5)
    assert len(seen) == 480 and canon_ray(psi2_spike) in seen
    print("[PASS] 2-qubit Clifford orbit of |ψ₂⟩ has size 480 and contains |ψ₂(1/2)⟩")

    # 5. Verify exact 4-qubit (16, 6, 2)-difference-set family F₄ = 20/9 + (1/81)|∑ e^{4iθ}|²
    diff_set = [0b0000, 0b0011, 0b0101, 0b0111, 0b1000, 0b1001]
    assert sorted(x ^ y for i, x in enumerate(diff_set) for y in diff_set[i + 1 :]) == list(range(1, 16))
    for angles in [
        [k * math.pi / 12.0 for k in range(6)],
        [0.0, math.pi / 4.0, 0.31, 0.31 + math.pi / 4.0, 1.17, 1.17 + math.pi / 4.0],
        [0.0, 0.2, 0.5, 0.9, 1.4, 2.1],
    ]:
        psi_s = [0j] * 16
        for x, th in zip(diff_set, angles):
            psi_s[x] = cmath.exp(1j * th) / math.sqrt(6.0)
        f_obs = pauli_moment4(psi_s, 4)
        zsum = sum(cmath.exp(4j * th) for th in angles)
        f_pred = 20.0 / 9.0 + (abs(zsum) ** 2) / 81.0
        assert abs(f_obs - f_pred) < 1e-12
    print("[PASS] 4-qubit bent-support (16,6,2)-difference-set identity F₄ = 20/9 + |∑ e^{4iθ}|²/81")

    # 6. Exact Q(√2, i) verification of closed-form phase states achieving F₃=9/4, F₄=45/16, F₅=21/8
    def q_add(u, v):
        return tuple(u[k] + v[k] for k in range(4))

    def q_sub(u, v):
        return tuple(u[k] - v[k] for k in range(4))

    def q_mul(u, v):
        a1, b1, c1, d1 = u
        a2, b2, c2, d2 = v
        return (
            a1 * a2 + 2 * b1 * b2 - (c1 * c2 + 2 * d1 * d2),
            a1 * b2 + b1 * a2 - (c1 * d2 + d1 * c2),
            a1 * c2 + 2 * b1 * d2 + c1 * a2 + 2 * d1 * b2,
            a1 * d2 + b1 * c2 + c1 * b2 + d1 * a2,
        )

    def q_conj(u):
        return (u[0], u[1], -u[2], -u[3])

    def q_norm2(u):
        a, b, c, d = u
        return (a * a + 2 * b * b + c * c + 2 * d * d, 2 * a * b + 2 * c * d)

    half = Fraction(1, 2)
    z0 = Fraction(0)
    z1 = Fraction(1)
    omega8 = [
        (z1, z0, z0, z0),
        (z0, half, z0, half),
        (z0, z0, z1, z0),
        (z0, -half, z0, half),
        (-z1, z0, z0, z0),
        (z0, -half, z0, -half),
        (z0, z0, -z1, z0),
        (z0, half, z0, -half),
    ]

    def exact_phase_moment4(n: int, m_fn) -> Fraction:
        N = 1 << n
        phi = [omega8[m_fn(x) % 8] for x in range(N)]
        tot_a, tot_b = z0, z0
        for a in range(N):
            w = [q_mul(q_conj(phi[x]), phi[x ^ a]) for x in range(N)]
            step = 1
            while step < N:
                for i in range(0, N, 2 * step):
                    for j in range(step):
                        u, v = w[i + j], w[i + j + step]
                        w[i + j] = q_add(u, v)
                        w[i + j + step] = q_sub(u, v)
                step <<= 1
            for b in range(N):
                na, nb = q_norm2(w[b])
                tot_a += na * na + 2 * nb * nb
                tot_b += 2 * na * nb
        assert tot_b == 0
        return tot_a / Fraction(N**4)

    def bits(x: int, n: int) -> list[int]:
        return [(x >> k) & 1 for k in range(n)]

    def m3(x: int) -> int:
        x0, x1, x2 = bits(x, 3)
        return x1 + x2 + 2 * x1 * x2 + 4 * x0 * x1 * x2

    def m4(x: int) -> int:
        x0, x1, x2, x3 = bits(x, 4)
        return x0 + x3 + 2 * x1 * x2 + 4 * x0 * x1 * (x2 + x3)

    def m5(x: int) -> int:
        x0, x1, x2, x3, x4 = bits(x, 5)
        return x1 + 2 * x0 * x2 + 2 * x1 * x3 + 4 * (x0 + x1) * x2 * x3 + 4 * x0 * x1 * x4

    assert exact_phase_moment4(3, m3) == Fraction(9, 4)
    assert exact_phase_moment4(4, m4) == Fraction(45, 16)
    assert exact_phase_moment4(5, m5) == Fraction(21, 8)

    # Also verify continuous parameter invariance at generic theta = 0.37
    for n, m_fn, shift_bit, target in [
        (3, m3, 0, 9.0 / 4.0),
        (4, m4, 2, 45.0 / 16.0),
        (5, m5, 0, 21.0 / 8.0),
    ]:
        N = 1 << n
        phi_c = [
            cmath.exp(1j * (m_fn(x) * math.pi / 4.0 + (0.37 if ((x >> shift_bit) & 1) else 0.0)))
            / math.sqrt(N)
            for x in range(N)
        ]
        # Fast WHT check
        tot = 0.0
        for a in range(N):
            w = [phi_c[x].conjugate() * phi_c[x ^ a] for x in range(N)]
            step = 1
            while step < N:
                for i in range(0, N, 2 * step):
                    for j in range(step):
                        u, v = w[i + j], w[i + j + step]
                        w[i + j] = u + v
                        w[i + j + step] = u - v
                step <<= 1
            tot += sum((z.real * z.real + z.imag * z.imag) ** 2 for z in w)
        assert abs(tot - target) < 1e-12
    print("[PASS] Exact closed-form continuous phase-state families: F₃=9/4, F₄=45/16, F₅=21/8")


if __name__ == "__main__":
    main()
