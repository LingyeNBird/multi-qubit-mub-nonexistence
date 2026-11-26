/*
 * Reproducible multi-start Riemannian L-BFGS optimization of the 4-qubit
 * Pauli fourth moment F_4(|psi>) = sum_{P in P_4} |<psi|P|psi>|^4 on CP^15.
 *
 * Companion numerical script for:
 *   "Non-Existence of Multi-Qubit Pauli-Covariant MUB Fiducial States and
 *    Alltop Phase Functions on F_2^n"
 *
 * Build & run:
 *   gcc -O3 -fopenmp scripts/cp15_riemannian_lbfgs.c -lm -o /tmp/cp15_opt
 *   /tmp/cp15_opt [n_starts=3000] [seed=20260401] [--extended]
 *
 * Method:
 *   - Initial states sampled independently from the Haar measure on CP^15
 *     (i.i.d. complex standard normal entries normalized to unit norm, using
 *     per-start SplitMix64 + Box-Muller PRNG for thread-independent
 *     reproducibility).
 *   - Exact Pauli expectations and Riemannian gradient grad_{CP^15} F_4
 *     computed in O(d^2 log d) via 4-qubit Fast Walsh-Hadamard Transforms.
 *   - Riemannian L-BFGS (memory m = 10) with sphere retraction
 *     R_psi(xi) = (psi + xi) / ||psi + xi||_2, orthogonal tangent-space
 *     vector transport, and Armijo backtracking line search.
 *   - Convergence tolerance: ||grad_{CP^15} F_4||_2 <= 1e-12 (max 600 iters).
 *   - Passing --extended also runs:
 *       (1) 4 independent seeds x 3,000 starts (12,000 total) with full
 *           sorted |<P>| Pauli-spectrum uniqueness check across cubic runs;
 *       (2) 200-chain x 25-hop basin hopping on CP^15;
 *       (3) Projected 30x30 Riemannian Hessian eigenvalue verification at
 *           analytic |psi_4(s*)> and the analytic 20/9 bent-support family.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define NQ 4
#define DIM 16
#define RVEC 32
#define LBFGS_M 10
#define MAX_ITER 600
#define GRAD_TOL 1e-12

/* Deterministic SplitMix64 PRNG (per-start independent stream). */
static inline uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static inline double rand_uniform(uint64_t *state) {
    /* Map to (0, 1) strictly away from 0 for Box-Muller safety. */
    return ((splitmix64(state) >> 11) + 0.5) * (1.0 / 9007199254740992.0);
}

static void sample_haar_cp15(uint64_t *state, double psi[RVEC]) {
    const double two_pi = 6.283185307179586476925286766559;
    double norm2 = 0.0;
    for (int i = 0; i < DIM; i++) {
        double u1 = rand_uniform(state);
        double u2 = rand_uniform(state);
        double r = sqrt(-2.0 * log(u1));
        psi[2 * i] = r * cos(two_pi * u2);
        psi[2 * i + 1] = r * sin(two_pi * u2);
        norm2 += psi[2 * i] * psi[2 * i] + psi[2 * i + 1] * psi[2 * i + 1];
    }
    double inv = 1.0 / sqrt(norm2);
    for (int i = 0; i < RVEC; i++) psi[i] *= inv;
}

static inline void fwht16(double v[DIM]) {
    for (int len = 1; len < DIM; len <<= 1) {
        for (int i = 0; i < DIM; i += (len << 1)) {
            for (int j = 0; j < len; j++) {
                double a = v[i + j];
                double b = v[i + j + len];
                v[i + j] = a + b;
                v[i + j + len] = a - b;
            }
        }
    }
}

static inline int parity4(int x) {
    x ^= x >> 2;
    x ^= x >> 1;
    return x & 1;
}

/*
 * Evaluate F_4(psi) and (if grad != NULL) the exact Riemannian gradient
 * grad_{CP^15} F_4(psi) in R^32 (interleaved re, im).
 * Assumes ||psi||_2 = 1.
 */
static double eval_f4_and_grad(const double psi[RVEC], double grad[RVEC]) {
    double f4 = 0.0;
    if (grad) {
        memset(grad, 0, sizeof(double) * RVEC);
    }

    for (int a = 0; a < DIM; a++) {
        double gr[DIM], gi[DIM];
        for (int x = 0; x < DIM; x++) {
            int xa = x ^ a;
            double xr = psi[2 * x], xi = psi[2 * x + 1];
            double yr = psi[2 * xa], yi = psi[2 * xa + 1];
            /* conj(psi[x]) * psi[x ^ a] */
            gr[x] = xr * yr + xi * yi;
            gi[x] = xr * yi - xi * yr;
        }
        fwht16(gr);
        fwht16(gi);

        double hr[DIM], hi[DIM];
        for (int b = 0; b < DIM; b++) {
            int p = parity4(a & b);
            /* eta(a,b) = 1 if p==0 else i; c = Re(eta * (gr + i*gi)) */
            double c = p ? -gi[b] : gr[b];
            double c2 = c * c;
            f4 += c2 * c2;
            if (grad) {
                double c3 = c2 * c;
                /* eta(a,b) * c^3 */
                hr[b] = p ? 0.0 : c3;
                hi[b] = p ? c3 : 0.0;
            }
        }

        if (grad) {
            fwht16(hr);
            fwht16(hi);
            for (int x = 0; x < DIM; x++) {
                int xa = x ^ a;
                double yr = psi[2 * xa], yi = psi[2 * xa + 1];
                /* 8 * (hr[x] + i*hi[x]) * psi[x ^ a] */
                grad[2 * x]     += 8.0 * (hr[x] * yr - hi[x] * yi);
                grad[2 * x + 1] += 8.0 * (hr[x] * yi + hi[x] * yr);
            }
        }
    }

    if (grad) {
        /* Project onto T_psi CP^15: subtract <psi, grad>_C * psi.
         * (Note: Re<psi, grad> = 8*f4, Im<psi, grad> = 0 analytically.) */
        double dot_re = 0.0, dot_im = 0.0;
        for (int x = 0; x < DIM; x++) {
            double pr = psi[2 * x], pi = psi[2 * x + 1];
            double gr_x = grad[2 * x], gi_x = grad[2 * x + 1];
            dot_re += pr * gr_x + pi * gi_x;
            dot_im += pr * gi_x - pi * gr_x;
        }
        for (int x = 0; x < DIM; x++) {
            double pr = psi[2 * x], pi = psi[2 * x + 1];
            grad[2 * x]     -= (dot_re * pr - dot_im * pi);
            grad[2 * x + 1] -= (dot_re * pi + dot_im * pr);
        }
    }
    return f4;
}

static inline double rdot(const double a[RVEC], const double b[RVEC]) {
    double s = 0.0;
    for (int i = 0; i < RVEC; i++) s += a[i] * b[i];
    return s;
}

static void project_tangent_cp15(const double psi[RVEC], double v[RVEC]) {
    double dot_re = 0.0, dot_im = 0.0;
    for (int x = 0; x < DIM; x++) {
        double pr = psi[2 * x], pi = psi[2 * x + 1];
        double vr = v[2 * x], vi = v[2 * x + 1];
        dot_re += pr * vr + pi * vi;
        dot_im += pr * vi - pi * vr;
    }
    for (int x = 0; x < DIM; x++) {
        double pr = psi[2 * x], pi = psi[2 * x + 1];
        v[2 * x]     -= (dot_re * pr - dot_im * pi);
        v[2 * x + 1] -= (dot_re * pi + dot_im * pr);
    }
}

static void retract_cp15(const double psi[RVEC], const double dir[RVEC],
                         double step, double out[RVEC]) {
    double n2 = 0.0;
    for (int i = 0; i < RVEC; i++) {
        out[i] = psi[i] + step * dir[i];
        n2 += out[i] * out[i];
    }
    double inv = 1.0 / sqrt(n2);
    for (int i = 0; i < RVEC; i++) out[i] *= inv;
}

typedef struct {
    double f_final;
    double gnorm_final;
    int iters;
    double psi_final[RVEC];
} RunResult;

static RunResult run_riemannian_lbfgs_from(const double psi_init[RVEC]) {
    double psi[RVEC], g[RVEC], psi_new[RVEC], g_new[RVEC];
    double s_hist[LBFGS_M][RVEC], y_hist[LBFGS_M][RVEC];
    double rho[LBFGS_M], alpha[LBFGS_M];
    int hist_len = 0, hist_head = 0;

    memcpy(psi, psi_init, sizeof(psi));
    double f = eval_f4_and_grad(psi, g);
    double gnorm = sqrt(rdot(g, g));
    int iter = 0;

    for (iter = 0; iter < MAX_ITER && gnorm > GRAD_TOL; iter++) {
        double q[RVEC], dir[RVEC];
        memcpy(q, g, sizeof(q));

        /* Two-loop L-BFGS recursion */
        for (int k = hist_len - 1; k >= 0; k--) {
            int idx = (hist_head - hist_len + k + LBFGS_M) % LBFGS_M;
            alpha[k] = rho[idx] * rdot(s_hist[idx], q);
            for (int i = 0; i < RVEC; i++) q[i] -= alpha[k] * y_hist[idx][i];
        }

        double gamma = 1.0;
        if (hist_len > 0) {
            int last = (hist_head - 1 + LBFGS_M) % LBFGS_M;
            double yy = rdot(y_hist[last], y_hist[last]);
            double sy = rdot(s_hist[last], y_hist[last]);
            if (yy > 1e-30 && sy > 0.0) gamma = sy / yy;
        }
        double rvec[RVEC];
        for (int i = 0; i < RVEC; i++) rvec[i] = gamma * q[i];

        for (int k = 0; k < hist_len; k++) {
            int idx = (hist_head - hist_len + k + LBFGS_M) % LBFGS_M;
            double beta = rho[idx] * rdot(y_hist[idx], rvec);
            for (int i = 0; i < RVEC; i++) rvec[i] += s_hist[idx][i] * (alpha[k] - beta);
        }
        for (int i = 0; i < RVEC; i++) dir[i] = -rvec[i];
        project_tangent_cp15(psi, dir);

        double slope = rdot(g, dir);
        if (slope >= 0.0) {
            /* Reset L-BFGS history if not a descent direction */
            for (int i = 0; i < RVEC; i++) dir[i] = -g[i];
            slope = -gnorm * gnorm;
            hist_len = 0;
        }

        /* Armijo backtracking line search (with near-machine-eps gradient safeguard) */
        double step = 1.0;
        const double c1 = 1e-4;
        double f_new = f;
        int accepted = 0;
        for (int ls = 0; ls < 40; ls++) {
            retract_cp15(psi, dir, step, psi_new);
            f_new = eval_f4_and_grad(psi_new, g_new);
            if (f_new <= f + c1 * step * slope) {
                accepted = 1;
                break;
            }
            /* When f is already at IEEE-754 double floor, accept full Newton-like step if ||grad|| drops */
            if (ls == 0 && f_new <= f + 1e-14 && sqrt(rdot(g_new, g_new)) < 0.8 * gnorm) {
                accepted = 1;
                break;
            }
            step *= 0.5;
        }
        if (!accepted) {
            if (hist_len > 0) {
                hist_len = 0;
                continue;
            }
            break;
        }

        /* Vector transport previous history pairs to T_{psi_new} CP^15 */
        for (int k = 0; k < hist_len; k++) {
            int idx = (hist_head - hist_len + k + LBFGS_M) % LBFGS_M;
            project_tangent_cp15(psi_new, s_hist[idx]);
            project_tangent_cp15(psi_new, y_hist[idx]);
            double sy = rdot(s_hist[idx], y_hist[idx]);
            rho[idx] = (sy > 1e-30) ? (1.0 / sy) : 0.0;
        }

        /* New transported step s_k = proj(psi_new - psi) and gradient difference y_k */
        double sk[RVEC], yk[RVEC], g_trans[RVEC];
        for (int i = 0; i < RVEC; i++) {
            sk[i] = psi_new[i] - psi[i];
            g_trans[i] = g[i];
        }
        project_tangent_cp15(psi_new, sk);
        project_tangent_cp15(psi_new, g_trans);
        for (int i = 0; i < RVEC; i++) yk[i] = g_new[i] - g_trans[i];

        double sy = rdot(sk, yk);
        if (sy > 1e-14 * sqrt(rdot(sk, sk) * rdot(yk, yk))) {
            memcpy(s_hist[hist_head], sk, sizeof(sk));
            memcpy(y_hist[hist_head], yk, sizeof(yk));
            rho[hist_head] = 1.0 / sy;
            hist_head = (hist_head + 1) % LBFGS_M;
            if (hist_len < LBFGS_M) hist_len++;
        }

        memcpy(psi, psi_new, sizeof(psi));
        memcpy(g, g_new, sizeof(g));
        f = f_new;
        gnorm = sqrt(rdot(g, g));
    }

    RunResult res;
    res.f_final = f;
    res.gnorm_final = gnorm;
    res.iters = iter;
    memcpy(res.psi_final, psi, sizeof(psi));
    return res;
}

static RunResult run_riemannian_lbfgs(uint64_t seed) {
    uint64_t st = seed;
    double psi_init[RVEC];
    sample_haar_cp15(&st, psi_init);
    return run_riemannian_lbfgs_from(psi_init);
}

static int verify_gradient(void) {
    uint64_t st = 123456789ULL;
    double psi[RVEC], g[RVEC], v[RVEC], p1[RVEC], p2[RVEC];
    sample_haar_cp15(&st, psi);
    sample_haar_cp15(&st, v);
    project_tangent_cp15(psi, v);
    eval_f4_and_grad(psi, g);
    double eps = 1e-6;
    retract_cp15(psi, v, eps, p1);
    retract_cp15(psi, v, -eps, p2);
    double fd = (eval_f4_and_grad(p1, NULL) - eval_f4_and_grad(p2, NULL)) / (2.0 * eps);
    double exact = rdot(g, v);
    double err = fabs(fd - exact) / (1.0 + fabs(exact));
    printf("Gradient check: exact=%.12f fd=%.12f rel_err=%.3e\n", exact, fd, err);
    return err < 1e-8;
}

static int cmp_double(const void *a, const void *b) {
    double da = *(const double *)a;
    double db = *(const double *)b;
    return (da > db) - (da < db);
}

static void sorted_pauli_abs_spectrum(const double psi[RVEC], double spec[256]) {
    int idx = 0;
    for (int a = 0; a < DIM; a++) {
        double gr[DIM], gi[DIM];
        for (int x = 0; x < DIM; x++) {
            int xa = x ^ a;
            double xr = psi[2 * x], xi = psi[2 * x + 1];
            double yr = psi[2 * xa], yi = psi[2 * xa + 1];
            gr[x] = xr * yr + xi * yi;
            gi[x] = xr * yi - xi * yr;
        }
        fwht16(gr);
        fwht16(gi);
        for (int b = 0; b < DIM; b++) {
            double c = parity4(a & b) ? -gi[b] : gr[b];
            spec[idx++] = fabs(c);
        }
    }
    qsort(spec, 256, sizeof(double), cmp_double);
}

static void build_analytic_cubic(double psi[RVEC]) {
    const double s = 0.62254319881646178125;
    double r = 1.0 - (15.0 / 16.0) * s;
    double al = sqrt(r);
    double mu = 2.0 * r - 1.0;
    double nu = sqrt(-1.0 + 4.0 * s - (15.0 / 4.0) * s * s);
    psi[0] = al;
    psi[1] = 0.0;
    for (int x = 1; x < DIM; x++) {
        psi[2 * x] = mu / (2.0 * al);
        psi[2 * x + 1] = nu / (2.0 * al);
    }
}

static void jacobi_eigs(int n, double *A, double *ev) {
    for (int sw = 0; sw < 120; sw++) {
        double off = 0.0;
        for (int i = 0; i < n; i++)
            for (int j = i + 1; j < n; j++) off += A[i * n + j] * A[i * n + j];
        if (off < 1e-24) break;
        for (int p = 0; p < n; p++) {
            for (int q = p + 1; q < n; q++) {
                double apq = A[p * n + q];
                if (fabs(apq) < 1e-300) continue;
                double th = (A[q * n + q] - A[p * n + p]) / (2.0 * apq);
                double t = (th >= 0.0 ? 1.0 : -1.0) / (fabs(th) + sqrt(th * th + 1.0));
                double c = 1.0 / sqrt(t * t + 1.0), s = t * c;
                for (int k = 0; k < n; k++) {
                    double a1 = A[k * n + p], a2 = A[k * n + q];
                    A[k * n + p] = c * a1 - s * a2;
                    A[k * n + q] = s * a1 + c * a2;
                }
                for (int k = 0; k < n; k++) {
                    double a1 = A[p * n + k], a2 = A[q * n + k];
                    A[p * n + k] = c * a1 - s * a2;
                    A[q * n + k] = s * a1 + c * a2;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) ev[i] = A[i * n + i];
    qsort(ev, (size_t)n, sizeof(double), cmp_double);
}

static void print_hessian_summary(const double psi[RVEC], const char *label) {
    double g0[RVEC];
    double f = eval_f4_and_grad(psi, g0);
    double B[30][RVEC], ipsi[RVEC];
    int nb = 0;
    for (int x = 0; x < DIM; x++) {
        ipsi[2 * x] = -psi[2 * x + 1];
        ipsi[2 * x + 1] = psi[2 * x];
    }
    for (int k = 0; k < RVEC && nb < 30; k++) {
        double v[RVEC] = {0};
        v[k] = 1.0;
        double a = rdot(v, psi), b = rdot(v, ipsi);
        for (int i = 0; i < RVEC; i++) v[i] -= a * psi[i] + b * ipsi[i];
        for (int j = 0; j < nb; j++) {
            double c = rdot(v, B[j]);
            for (int i = 0; i < RVEC; i++) v[i] -= c * B[j][i];
        }
        double nv = sqrt(rdot(v, v));
        if (nv < 1e-6) continue;
        for (int i = 0; i < RVEC; i++) B[nb][i] = v[i] / nv;
        nb++;
    }
    double H[900], ev[30], eps = 1e-6;
    for (int j = 0; j < 30; j++) {
        double p1[RVEC], p2[RVEC], g1[RVEC], g2[RVEC];
        retract_cp15(psi, B[j], eps, p1);
        retract_cp15(psi, B[j], -eps, p2);
        eval_f4_and_grad(p1, g1);
        eval_f4_and_grad(p2, g2);
        for (int i = 0; i < 30; i++) H[i * 30 + j] = (rdot(g1, B[i]) - rdot(g2, B[i])) / (2.0 * eps);
    }
    for (int i = 0; i < 30; i++)
        for (int j = i + 1; j < 30; j++) {
            double m = 0.5 * (H[i * 30 + j] + H[j * 30 + i]);
            H[i * 30 + j] = H[j * 30 + i] = m;
        }
    jacobi_eigs(30, H, ev);
    printf("  [%s] F=%.12f |grad|=%.2e  eigs[0..4]=(%.2e, %.2e, %.2e, %.3f, %.3f) max=%.3f\n",
           label, f, sqrt(rdot(g0, g0)), ev[0], ev[1], ev[2], ev[3], ev[4], ev[29]);
}

static void run_batch(int n_starts, uint64_t base_seed, const double ref_spec[256],
                      int verbose_clusters) {
    const double F4_CUBIC = 2.1505201547139396;
    RunResult *results = (RunResult *)malloc(sizeof(RunResult) * (size_t)n_starts);
    double *vals = (double *)malloc(sizeof(double) * (size_t)n_starts);
    if (!results || !vals) exit(1);

    #pragma omp parallel for schedule(dynamic, 16)
    for (int r = 0; r < n_starts; r++) {
        uint64_t seed = base_seed + 0x9e3779b97f4a7c15ULL * (uint64_t)(r + 1);
        results[r] = run_riemannian_lbfgs(seed);
    }

    double min_f = 1e100, max_gnorm = 0.0, max_spec_diff = 0.0;
    int converged_count = 0, cubic_hits = 0, cubic_conv = 0, sec_hits = 0, sec_conv = 0;
    int below_cubic = 0;
    long long total_iters = 0;

    for (int r = 0; r < n_starts; r++) {
        vals[r] = results[r].f_final;
        if (results[r].f_final < min_f) min_f = results[r].f_final;
        if (results[r].gnorm_final > max_gnorm) max_gnorm = results[r].gnorm_final;
        if (results[r].gnorm_final <= GRAD_TOL) converged_count++;
        if (fabs(results[r].f_final - F4_CUBIC) < 1e-10) {
            cubic_hits++;
            if (results[r].gnorm_final <= GRAD_TOL) cubic_conv++;
            double sp[256];
            sorted_pauli_abs_spectrum(results[r].psi_final, sp);
            for (int k = 0; k < 256; k++) {
                double d = fabs(sp[k] - ref_spec[k]);
                if (d > max_spec_diff) max_spec_diff = d;
            }
        } else if (fabs(results[r].f_final - 20.0 / 9.0) < 1e-6) {
            sec_hits++;
            if (results[r].gnorm_final <= GRAD_TOL) sec_conv++;
        }
        if (results[r].f_final < F4_CUBIC - 1e-10) below_cubic++;
        total_iters += results[r].iters;
    }

    qsort(vals, (size_t)n_starts, sizeof(double), cmp_double);

    printf("\n=== CP^15 Multi-Start Riemannian L-BFGS Summary ===\n");
    printf("Starts            : %d (base_seed=%llu)\n", n_starts, (unsigned long long)base_seed);
    printf("Converged (<=1e-12): %d / %d (cubic %d/%d, 20/9 %d/%d, max_gnorm=%.3e, avg_iters=%.1f)\n",
           converged_count, n_starts, cubic_conv, cubic_hits, sec_conv, sec_hits,
           max_gnorm, (double)total_iters / n_starts);
    printf("Minimum F_4       : %.15f (F4_cubic = %.15f, diff = %.3e)\n",
           min_f, F4_CUBIC, min_f - F4_CUBIC);
    printf("Hits at F4_cubic  : %d / %d (%.2f%%, max sorted |<P>| diff = %.3e)\n",
           cubic_hits, n_starts, 100.0 * cubic_hits / n_starts, max_spec_diff);
    printf("Hits at 20/9      : %d / %d (%.2f%%)\n",
           sec_hits, n_starts, 100.0 * sec_hits / n_starts);
    printf("Strictly below    : %d\n", below_cubic);

    if (verbose_clusters) {
        printf("\nDistinct converged clusters (tol 1e-6):\n");
        int i = 0;
        while (i < n_starts) {
            int j = i + 1;
            while (j < n_starts && fabs(vals[j] - vals[i]) < 1e-6) j++;
            double mean = 0.0;
            for (int k = i; k < j; k++) mean += vals[k];
            mean /= (j - i);
            printf("  F_4 = %.12f  (M_2 = %.9f) : %5d runs (%.2f%%)\n",
                   mean, -log(mean / 16.0), j - i, 100.0 * (j - i) / n_starts);
            i = j;
        }
    }

    free(results);
    free(vals);
}

int main(int argc, char **argv) {
    int n_starts = 3000;
    uint64_t base_seed = 20260401ULL;
    int extended = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--extended") == 0) {
            extended = 1;
        } else if (i == 1) {
            n_starts = atoi(argv[i]);
        } else if (i == 2) {
            base_seed = strtoull(argv[i], NULL, 10);
        }
    }

    if (!verify_gradient()) {
        fprintf(stderr, "ERROR: Riemannian gradient verification failed!\n");
        return 1;
    }

    double ref_psi[RVEC], ref_spec[256];
    build_analytic_cubic(ref_psi);
    sorted_pauli_abs_spectrum(ref_psi, ref_spec);

    run_batch(n_starts, base_seed, ref_spec, 1);

    if (extended) {
        printf("\n=== Extended Verification: Additional Independent Seeds ===\n");
        uint64_t extra_seeds[3] = {987654321ULL, 314159265ULL, 271828182ULL};
        for (int s = 0; s < 3; s++) run_batch(3000, extra_seeds[s], ref_spec, 0);

        printf("\n=== Extended Verification: Basin Hopping (200 chains x 25 hops) ===\n");
        const double F4_CUBIC = 2.1505201547139396;
        int bh_cubic = 0, bh_below = 0;
        double bh_min = 1e100;
        #pragma omp parallel for reduction(+:bh_cubic,bh_below) schedule(dynamic, 4)
        for (int c = 0; c < 200; c++) {
            uint64_t st = 0xCAFEBABEULL + 1000003ULL * (uint64_t)(c + 1);
            double init[RVEC], best_psi[RVEC];
            sample_haar_cp15(&st, init);
            RunResult best = run_riemannian_lbfgs_from(init);
            memcpy(best_psi, best.psi_final, sizeof(best_psi));
            for (int hop = 0; hop < 25; hop++) {
                double v[RVEC], cand[RVEC];
                sample_haar_cp15(&st, v);
                project_tangent_cp15(best_psi, v);
                double nv = sqrt(rdot(v, v));
                for (int i = 0; i < RVEC; i++) v[i] /= nv;
                double step = 0.35 + 0.50 * rand_uniform(&st);
                retract_cp15(best_psi, v, step, cand);
                RunResult cur = run_riemannian_lbfgs_from(cand);
                if (cur.f_final < best.f_final - 1e-12) {
                    best = cur;
                    memcpy(best_psi, cur.psi_final, sizeof(best_psi));
                }
            }
            if (fabs(best.f_final - F4_CUBIC) < 1e-10) bh_cubic++;
            if (best.f_final < F4_CUBIC - 1e-10) bh_below++;
            #pragma omp critical
            { if (best.f_final < bh_min) bh_min = best.f_final; }
        }
        printf("  Basin hopping: reached F4_cubic = %d / 200, strictly below = %d, min F_4 = %.15f\n",
               bh_cubic, bh_below, bh_min);

        printf("\n=== Extended Verification: Projected 30x30 Riemannian Hessian ===\n");
        print_hessian_summary(ref_psi, "analytic |psi_4(s*)>");
        const int S6[6] = {0, 3, 5, 7, 8, 9};
        double psi20[RVEC] = {0};
        const double pi = 3.14159265358979323846;
        for (int k = 0; k < 6; k++) {
            double th = k * pi / 12.0;
            psi20[2 * S6[k]] = cos(th) / sqrt(6.0);
            psi20[2 * S6[k] + 1] = sin(th) / sqrt(6.0);
        }
        print_hessian_summary(psi20, "analytic 20/9 bent-support (theta_k = k*pi/12)");
    }

    return 0;
}
