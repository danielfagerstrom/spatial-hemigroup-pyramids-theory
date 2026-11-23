# Copied unchanged from the hub, offices/postdoc/experiments/grid_pyramid_exactness.py (P-0001; Q-0630).
"""Is the sampled Matern pyramid "exact at every level"?

Postdoc office, 2026-09-07, brief on Paper VI (spatial-hemigroup-pyramids).
Tests Proposition 3.1(2) of `draft/spatial-hemigroup-pyramids.md`, which reads

    "the Matern pyramid of Theorem 2.17 sampled on the grids q^n h Z is exact at
     every level, each level being one forward-backward lag section on the current
     grid followed by decimation, with the same coefficients at every level."

Two objects are compared.

  A_n  the ARRAY THE ALGORITHM PRODUCES: start from a unit impulse on the grid h Z,
       and n times over, convolve with the sampled Laplace (two-sided geometric,
       ratio a = exp(-h/(c t)) in the CURRENT grid's units, so the same coefficient
       at every level) and decimate by q.

  S_n  the SAMPLED CONTINUUM LEVEL: the level-n kernel of the continuum Matern
       pyramid, i.e. the convolution of Laplace kernels of ranges c t, c t q, ...,
       c t q^{n-1}, evaluated on the coarse grid q^n h Z and normalised.

  G_n  a third candidate: the convolution, ON THE COARSE GRID, of the sampled
       Laplace kernels of the same ranges.  (Included because it is the reading
       under which "the same array at every level" is a statement about grid
       kernels rather than about samples of continuum kernels.)

If Proposition 3.1(2) is exact, A_n == S_n to machine precision for every n and
every h/(c t).  Reported: total-variation distance and max relative error.

Also checked, cheaply:
  * the log-series Levy measure of the two-sided geometric,
        -log lambda_a(theta) = 2 sum_{n>=1} (a^n / n) (1 - cos n theta),
    which is what makes the grid family infinitely divisible and lets one write
    the exponent of the limit of the equivalent weighting functions;
  * the dilogarithm limit of Theorem 2.17(5).

Run:  uv run --no-project --with numpy python grid_pyramid_exactness.py
"""

import numpy as np

Q = 2
C = 1.0
T0 = 1.0


def geom(a, m):
    """Two-sided geometric (sampled Laplace) on indices -m..m, unit mass."""
    n = np.arange(-m, m + 1)
    w = a ** np.abs(n)
    return w / w.sum()


def laplace_conv_density(x, ranges):
    """Density of a convolution of Laplace kernels with DISTINCT ranges b_k.

    transform prod_k 1/(1 + b_k^2 w^2)  ->  sum_k A_k * exp(-|x|/b_k)/(2 b_k),
    A_k = prod_{j != k} 1/(1 - b_j^2/b_k^2).
    """
    b = np.asarray(ranges, dtype=float)
    out = np.zeros_like(np.asarray(x, dtype=float))
    for k, bk in enumerate(b):
        ak = 1.0
        for j, bj in enumerate(b):
            if j != k:
                ak /= 1.0 - (bj * bj) / (bk * bk)
        out = out + ak * np.exp(-np.abs(x) / bk) / (2.0 * bk)
    return out


def pyramid_levels(rho, nlev, m0=1 << 15):
    """A_n for n = 1..nlev.  rho = h/(c t) is fixed across levels by covariance."""
    a = np.exp(-rho)
    arr = np.zeros(2 * m0 + 1)
    arr[m0] = 1.0                     # unit impulse on the fine grid
    m = m0
    out = []
    for _ in range(nlev):
        k = geom(a, m)                # ratio a in the CURRENT grid's units
        arr = np.convolve(arr, k, mode="same")
        arr = arr[m % Q:: Q]          # decimate, keeping the sample at the origin
        m = (len(arr) - 1) // 2
        arr = arr[len(arr) // 2 - m: len(arr) // 2 + m + 1]
        arr = arr / arr.sum()
        out.append(arr.copy())
    return out


def compare(rho, nlev=4):
    print(f"\n--- h/(c t) = {rho} ---")
    A = pyramid_levels(rho, nlev)
    for n in range(1, nlev + 1):
        an = A[n - 1]
        m = (len(an) - 1) // 2
        h_n = rho * Q ** n                        # coarse spacing in units of c t
        x = np.arange(-m, m + 1) * h_n
        ranges = [C * T0 * Q ** k for k in range(n)]
        sn = laplace_conv_density(x, ranges)
        sn = sn / sn.sum()
        gn = None
        for b in ranges:
            g = geom(np.exp(-h_n / b), m)
            gn = g if gn is None else np.convolve(gn, g, mode="same")
        gn = gn / gn.sum()
        tv_s = 0.5 * np.abs(an - sn).sum()
        tv_g = 0.5 * np.abs(an - gn).sum()
        rel_s = np.abs(an - sn).max() / sn.max()
        print(
            f"  level {n}:  TV(A,S) = {tv_s:.3e}   max-rel(A,S) = {rel_s:.3e}"
            f"   TV(A,G) = {tv_g:.3e}"
        )


def check_log_series(a=0.6, theta=0.9):
    lam = (1 - a) ** 2 / (1 - 2 * a * np.cos(theta) + a * a)
    series = 2 * sum((a ** n) / n * (1 - np.cos(n * theta)) for n in range(1, 4000))
    print(f"\nlog-series Levy measure: -log lambda = {-np.log(lam):.12f}"
          f"   series = {series:.12f}")


def check_dilog(c=1.0, w=1.7):
    lhs = []
    for q in (1.2, 1.05, 1.01, 1.002):
        ell = np.log(q)
        f = sum(np.log(1 + c * c * q ** (-2 * i) * w * w) for i in range(1, 200000))
        lhs.append((q, ell * f))
    # -1/2 Li_2(-c^2 w^2) by series/integral
    from math import log
    u = np.linspace(0, 60, 2_000_001)
    rhs = np.trapezoid(np.log(1 + c * c * w * w * np.exp(-2 * u)), u)
    print("\nTheorem 2.17(5), ell*F_q(w) -> -Li_2(-c^2 w^2)/2 :")
    for q, v in lhs:
        print(f"   q = {q:<7} ell*F_q = {v:.8f}")
    print(f"   integral = {rhs:.8f}")
    _ = log


if __name__ == "__main__":
    for rho in (1.0, 0.5, 0.25, 0.1):
        compare(rho)
    check_log_series()
    check_dilog()
