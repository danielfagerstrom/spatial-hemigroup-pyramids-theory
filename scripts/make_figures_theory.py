# /// script
# requires-python = ">=3.10"
# dependencies = ["numpy", "scipy", "matplotlib"]
# ///
"""The data figures of the theory paper (paper/), one for each of Sections 3 to 6.

    uv run scripts/make_figures_theory.py

writes four files into figures/:

  theory-strata.png    Section 3. The family of Proposition prop:stratum-two-example in the plane,
                       d = 2, q = 2, h = 1, with the weights w_i = 1 for i < 0 and w_i = 0 for
                       i >= 0 that Theorem thm:lattice-strata-strict uses. Its ladder step rho has the
                       Levy measure sigma_h (unit mass on the circle of radius h). Left: the partial
                       products prod_{m=1}^M rho^(q^{-m} omega) of Proposition
                       prop:ladder-knot-kernel(1), M = 1, 2, 4, 8, and their limit, the transform of
                       the knot kernel mu_1. Right: Psi_1(omega) - log_q(h|omega|) against
                       log_q(h|omega|), beside the same for the exponent F of the isotropic origin
                       datum (a_0, k_2) = (0, (log q)^{-1} 1_{(0,h)}) (Definition
                       def:isotropic-origin-data), which is in A_2 (Theorem thm:cited-A35) and spreads
                       the same jumps evenly in log length.
  theory-grid-steps.png
                       Section 4. Proposition prop:sampled-laplace-exact(2) with q = 2, h = 1: the
                       computed array U_n against the sampled step V_n. Left: U_3 and V_3 at ct = h, in
                       the units of the grid q^3 h Z. Right: U_n(m) - V_n(m) for the levels n = 1 to 4
                       at h/(ct) = 1 (the size of the difference over the ratios h/(ct) is Table
                       tab:grid-pyramid-error, by scripts/grid_pyramid_exactness.py).
  theory-creation.png  Section 5. Proposition prop:creation-plane(1) in the plane, d = 2, for the
                       octave step mu = L_r of the Matern pyramid, r = 1: the witness f_{a,delta} at
                       a = 5/2, delta = 1/100, and L_r * f. Left and middle: the two functions, with the
                       level set at alpha; right: both on the axis x_2 = 0.
  theory-frame.png     Section 6. Proposition prop:grid-pyramid-not-isotropic(3) on h Z^2, q = 2, for
                       the sampled Laplace mask with a = e^{-h/c}, h/c = 1/2, the frame Matern grid
                       pyramid. Left: the atoms of its Levy measure nu_1, display (eq:frame-levy), in
                       the square |x_i| <= 1.1 h, each mass summed over the terms m <= 7. Middle: the
                       atoms of the Levy measure nu_w of the five-point resolvent mask kappa_t, t = h
                       (p = 4/5), Proposition prop:resolvent-masks-exact(1),(4), on |n_i| <= 6, with
                       the ratio of the masses at 5h e_1 and (3h, 4h), two lattice points of one
                       circle. Right: the level sets of the transform of its
                       knot kernel, against those of the Matern pyramid's knot kernel
                       exp(-F_q(|omega|)) of Theorem thm:matern-pyramid with the same c, which are
                       circles.

Every number shown is computed here: Bessel sums and quadratures by scipy, the plane convolution of
Section 5 by the discrete Fourier transform on a periodic grid, fine across the ridge. The figures
assert nothing the statements of the paper do not.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LogNorm
from scipy.integrate import cumulative_trapezoid, quad
from scipy.ndimage import maximum_filter
from scipy.special import j0

HERE = Path(__file__).resolve().parent
FIG = HERE.parent / "figures"
BLUE, ORANGE, GREEN, PURPLE, GREY = "#1b6ca8", "#c1531b", "#2a8a4a", "#6b4c9a", "0.45"


# ----------------------------------------------------------------------------- Section 3

def strata(path, q=2.0, h=1.0):
    """The ladder of the stratum-2 witness and its exponent against a fully covariant one."""
    rho = np.logspace(-1, np.log10(2.0e3), 1200)        # rho = h |omega|
    term = lambda m, r: 1.0 - j0(q ** (-m) * r)          # psi_step(q^{-m} omega), step = sigma_h
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.9), constrained_layout=True)

    shades = {1: "#9ecae1", 2: "#6baed6", 4: "#3182bd", 8: "#08519c"}
    for M, col in shades.items():
        psi = sum(term(m, rho) for m in range(1, M + 1))
        ax1.loglog(rho, np.exp(-psi), color=col, lw=1.1, label=f"$M = {M}$")
    psi1 = sum(term(m, rho) for m in range(1, 90))
    ax1.loglog(rho, np.exp(-psi1), color="k", lw=1.5, label=r"limit $\widehat{\mu}_1$")
    ax1.set_xlabel(r"$h|\omega|$")
    ax1.set_ylabel("transform")
    ax1.set_ylim(1e-5, 1.5)
    ax1.set_title(r"partial products $\prod_{m=1}^{M}\widehat\varrho(q^{-m}\omega)$", fontsize=10)
    ax1.legend(fontsize=8, loc="lower left")

    # Psi_1 of the stratum-2 family against the exponent F of the profile (log q)^{-1} 1_{(0,h)}
    ell = np.linspace(0.0, 9.0, 40001)                   # ell = log_q(h |omega|)
    r = q ** ell
    psi = sum(term(m, r) for m in range(1, 90))
    u = np.linspace(0.0, r.max() * 1.001, 4_000_001)
    integrand = np.empty_like(u)
    integrand[0] = 0.0
    integrand[1:] = (1.0 - j0(u[1:])) / u[1:]
    F_cum = cumulative_trapezoid(integrand, u, initial=0.0) / np.log(q)
    F = np.interp(r, u, F_cum)
    ax2.plot(ell, psi - ell, color=BLUE, lw=1.3, label=r"$\Psi_1$, stratum 2 (spheres $hq^i$)")
    ax2.plot(ell, F - ell, color=ORANGE, lw=1.3, label=r"$F$, stratum 3 (profile $\mathbf{1}_{(0,h)}/\log q$)")
    for k in range(0, 10):
        ax2.axvline(k, color="0.85", lw=0.6, zorder=0)
    ax2.set_xlabel(r"$\log_q(h|\omega|)$")
    ax2.set_ylabel(r"exponent $-\ \log_q(h|\omega|)$")
    ax2.set_title("one ratio against every ratio", fontsize=10)
    ax2.legend(fontsize=8, loc="upper right")
    fig.savefig(path, dpi=160)
    plt.close(fig)
    tail = (ell >= 7) & (ell <= 9)
    return {"osc_psi": float(np.ptp((psi - ell)[tail])), "osc_F": float(np.ptp((F - ell)[tail]))}


# ----------------------------------------------------------------------------- Section 4

def _laplace_sum_density(x, taus):
    """Density of L_{tau_0} * ... * L_{tau_{n-1}} on the line, distinct ranges, by partial fractions."""
    out = np.zeros_like(x, dtype=float)
    for k, tk in enumerate(taus):
        A = np.prod([tk ** 2 / (tk ** 2 - tj ** 2) for j, tj in enumerate(taus) if j != k])
        out += A * np.exp(-np.abs(x) / tk) / (2.0 * tk)
    return out


def computed_level(n, ct, q=2, h=1.0):
    """U_n: u_{k+1}(m) = (g * u_k)(qm) from u_0 = delta_0, g the sampled Laplace kernel of range ct."""
    a = np.exp(-h / ct)
    M = int(np.ceil(45 * ct / h)) + 5                     # a^M < 1e-19
    g = (1 - a) / (1 + a) * a ** np.abs(np.arange(-M, M + 1))
    u, c = np.array([1.0]), 0                             # c: the index of the origin
    for _ in range(n):
        v = np.convolve(u, g)
        c += M
        u, c = v[c % q::q], c // q
    return np.arange(len(u)) - c, u / u.sum()


def sampled_step(n, ct, m, q=2, h=1.0):
    """V_n: the step L_{ct} * ... * L_{ct q^{n-1}} sampled on q^n h Z, renormalized to unit mass."""
    taus = [ct * q ** k for k in range(n)]
    wide = q ** n * h * np.arange(-6000, 6001)
    return _laplace_sum_density(q ** n * h * m, taus) / _laplace_sum_density(wide, taus).sum()


def grid_steps(path, q=2, h=1.0):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.8), constrained_layout=True)
    m, U = computed_level(3, 1.0, q, h)
    V = sampled_step(3, 1.0, m, q, h)
    sel = np.abs(m) <= 4
    ax1.plot(m[sel] - 0.08, U[sel], "o", color=BLUE, ms=5, label=r"$U_3$, computed")
    ax1.plot(m[sel] + 0.08, V[sel], "s", mfc="none", color=ORANGE, ms=5, label=r"$V_3$, sampled step")
    ax1.vlines(m[sel] - 0.08, 0, U[sel], color=BLUE, lw=0.8)
    ax1.vlines(m[sel] + 0.08, 0, V[sel], color=ORANGE, lw=0.8)
    ax1.set_xlabel(r"$m$ (grid $q^3h\mathbb{Z}$)")
    ax1.set_ylabel("mass")
    ax1.set_title(r"level $n = 3$, $h/(ct) = 1$, $q = 2$", fontsize=10)
    ax1.legend(fontsize=8)

    shades = {1: "0.55", 2: "#9ecae1", 3: "#3182bd", 4: "#08519c"}
    out = {}
    for n, col in shades.items():
        mm, U = computed_level(n, 1.0, q, h)
        diff = U - sampled_step(n, 1.0, mm, q, h)
        out[n] = float(np.abs(diff).max())
        s = np.abs(mm) <= 4
        ax2.plot(mm[s], diff[s], marker="o", ms=4, lw=1.1, color=col,
                 label=f"$n = {n}$" + (r", $U_1 = V_1$" if n == 1 else ""))
    ax2.axhline(0, color="0.8", lw=0.6, zorder=0)
    ax2.set_xlabel(r"$m$ (grid $q^nh\mathbb{Z}$)")
    ax2.set_title(r"$U_n(m) - V_n(m)$, $h/(ct) = 1$", fontsize=10)
    ax2.legend(fontsize=8)
    fig.savefig(path, dpi=160)
    plt.close(fig)
    return {"max_abs_diff_by_level": out}


# ----------------------------------------------------------------------------- Section 5

def creation(path, a=2.5, delta=0.01, r=1.0):
    """The witness f_{a,delta} in the plane and L_r * f, by the transform (1 + r^2|omega|^2)^{-1}."""
    L1, L2, dx1, dx2 = 18.0, 8.0, 0.04, delta / 6
    n1, n2 = int(round(2 * L1 / dx1)), int(round(2 * L2 / dx2))
    x1 = (np.arange(n1) - n1 // 2) * dx1
    x2 = (np.arange(n2) - n2 // 2) * dx2
    X1, X2 = np.meshgrid(x1, x2, indexing="ij")
    f = (np.exp(-((X1 - a) ** 2 + X2 ** 2) / 2) + np.exp(-((X1 + a) ** 2 + X2 ** 2) / 2)
         + 8 * a * a * np.exp(-X1 ** 2 / (8 * a * a)) * np.exp(-X2 ** 2 / (2 * delta ** 2)))
    W1, W2 = np.meshgrid(2 * np.pi * np.fft.fftfreq(n1, dx1), 2 * np.pi * np.fft.rfftfreq(n2, dx2),
                         indexing="ij")
    u = np.fft.irfft2(np.fft.rfft2(f) / (1.0 + r * r * (W1 ** 2 + W2 ** 2)), s=f.shape)

    def maxima(v):
        peak = (v == maximum_filter(v, size=3, mode="nearest")) & (v > 1e-3 * v.max())
        return [(x1[i], x2[j]) for i, j in np.argwhere(peak)]

    mf, mu = maxima(f), maxima(u)
    i0, j0_ = n1 // 2, n2 // 2
    saddle, top = u[i0, j0_], max(u[i, j] for i, j in np.argwhere(
        (u == maximum_filter(u, size=3, mode="nearest")) & (u > 1e-3 * u.max())))
    alpha = 0.5 * (saddle + top)

    # The proof of clause (1) takes a with W < m/2 on |x| >= 2a - 1, where W := mu * e^{-|x|^2/2}
    # and m := W(0) - max_{|x|=1} W; W is radial, W(R) = int rho e^{-rho^2/2} J_0(rho R) /
    # (1 + r^2 rho^2) d rho by the transform.
    W = lambda R: quad(lambda p: p * np.exp(-p * p / 2) * j0(p * R) / (1 + r * r * p * p),
                       0, 60, limit=400)[0]
    m_proof = W(0.0) - W(1.0)
    a_ok = W(2 * a - 1) < m_proof / 2

    # the display window
    w1 = np.abs(x1) <= a + 3.0
    w2 = np.abs(x2) <= 2.5
    fig, axes = plt.subplots(1, 3, figsize=(12.0, 3.6), constrained_layout=True,
                             gridspec_kw={"width_ratios": [1, 1, 1.05]})
    ext = (x1[w1][0], x1[w1][-1], x2[w2][0], x2[w2][-1])
    fw, uw = f[np.ix_(w1, w2)], u[np.ix_(w1, w2)]
    im0 = axes[0].imshow(fw.T, origin="lower", extent=ext, aspect="equal", cmap="Greys",
                         norm=LogNorm(vmin=1e-2, vmax=f.max()), interpolation="antialiased")
    axes[0].contour(x1[w1], x2[w2], fw.T, levels=[alpha], colors=ORANGE, linewidths=1.0)
    im1 = axes[1].imshow(uw.T, origin="lower", extent=ext, aspect="equal", cmap="Greys",
                         interpolation="antialiased")
    axes[1].contour(x1[w1], x2[w2], uw.T, levels=[alpha], colors=ORANGE, linewidths=1.0)
    for ax, pts, title in ((axes[0], mf, r"$f = f_{a,\delta}$: one local maximum"),
                           (axes[1], mu, r"$L_r * f$: two local maxima")):
        ax.plot([p[0] for p in pts], [p[1] for p in pts], "+", color=BLUE, ms=9, mew=1.6)
        ax.set_title(title, fontsize=10)
        ax.set_xlabel(r"$x_1$")
        ax.set_ylabel(r"$x_2$")
    fig.colorbar(im0, ax=axes[0], shrink=0.7)
    fig.colorbar(im1, ax=axes[1], shrink=0.7)

    ax = axes[2]
    ax.semilogy(x1[w1], f[w1, j0_], color="k", lw=1.2, label=r"$f(x_1, 0)$")
    ax.semilogy(x1[w1], u[w1, j0_], color=BLUE, lw=1.4, label=r"$(L_r * f)(x_1, 0)$")
    ax.axhline(alpha, color=ORANGE, lw=1.0, ls="--", label=r"level $\alpha$")
    ax.set_xlabel(r"$x_1$")
    ax.set_title("on the axis $x_2 = 0$", fontsize=10)
    ax.set_ylim(0.3, 120)
    ax.legend(fontsize=8, loc="center")
    fig.savefig(path, dpi=160)
    plt.close(fig)
    return {"f_maxima": len(mf), "u_maxima": len(mu), "u_peaks": [round(p[0], 2) for p in mu],
            "saddle": float(saddle), "top": float(top), "alpha": float(alpha), "f0": float(f.max()),
            "proof_m": m_proof, "W(2a-1)": W(2 * a - 1), "a_meets_proof": a_ok}


# ----------------------------------------------------------------------------- Section 6

def frame(path, q=2.0, h=1.0, c=2.0, levels=(0.1, 0.3, 0.5, 0.7, 0.9)):
    """The frame Matern grid pyramid's Levy measure on the axes, and its knot kernel's level sets.

    Drawn 13.8 in wide and printed at the text width, about 0.45 of that, so the fonts are set
    about twice the usual size to print at 7-9 pt (review r1, part B, finding 19).
    """
    plt.rcParams.update({"axes.labelsize": 17, "xtick.labelsize": 15, "ytick.labelsize": 15})
    a = np.exp(-h / c)
    atoms = {}
    for m in range(1, 8):
        for n in range(1, 400):
            x = n * h * q ** (-m)
            if x > 1.1 * h:
                break
            key = round(x * 2 ** 7)                       # exact on the dyadic grid h 2^{-7} Z
            atoms[key] = atoms.get(key, 0.0) + a ** n / n
    pos = np.array(sorted(atoms)) / 2 ** 7
    mass = np.array([atoms[k] for k in sorted(atoms)])
    fig, (ax1, ax3, ax2) = plt.subplots(1, 3, figsize=(13.8, 5.4), constrained_layout=True)
    s = 160 * mass / mass.max()
    for sign in (1, -1):
        ax1.scatter(sign * pos, 0 * pos, s=s, color=BLUE, lw=0, zorder=3)
        ax1.scatter(0 * pos, sign * pos, s=s, color=BLUE, lw=0, zorder=3)
    rad = 0.75 * h
    ax1.add_patch(plt.Circle((0, 0), rad, fill=False, ls="--", lw=0.9, color=ORANGE))
    ax1.plot([rad, -rad, 0, 0], [0, 0, rad, -rad], "o", mfc="none", mec=ORANGE, ms=9, mew=1.2)
    ax1.set_aspect("equal")
    ax1.set_xlim(-1.15 * h, 1.15 * h)
    ax1.set_ylim(-1.15 * h, 1.15 * h)
    ax1.set_xlabel(r"$x_1/h$")
    ax1.set_ylabel(r"$x_2/h$")
    ax1.set_title("frame mask:\natoms of $\\nu_1$ on the axes", fontsize=16)

    five = five_point_levy()
    nu, K = five["nu"], five["K"]
    box = 6
    idx = np.arange(-box, box + 1)
    X, Y = np.meshgrid(idx, idx, indexing="ij")
    vals = nu[K - box:K + box + 1, K - box:K + box + 1]
    keep = (X != 0) | (Y != 0)
    sc = ax3.scatter(X[keep], Y[keep], s=34, c=vals[keep], cmap="Blues", norm=LogNorm(), lw=0,
                     zorder=3)
    cb = fig.colorbar(sc, ax=ax3, shrink=0.8)
    cb.set_label(r"mass of the atom", fontsize=15)
    cb.ax.tick_params(labelsize=13)
    ax3.add_patch(plt.Circle((0, 0), 5, fill=False, ls="--", lw=0.9, color=ORANGE))
    ring = [(i, j) for i in idx for j in idx if i * i + j * j == 25]
    ax3.plot([r[0] for r in ring], [r[1] for r in ring], "o", mfc="none", mec=ORANGE, ms=9, mew=1.2)
    ax3.set_aspect("equal")
    ax3.set_xlim(-box - 0.6, box + 0.6)
    ax3.set_ylim(-box - 0.6, box + 0.6)
    ax3.set_xlabel("$x_1/h$\n$\\nu_w(\\{5he_1\\})\\,/\\,\\nu_w(\\{(3h, 4h)\\}) = %.2f$"
                   % (five["m50"] / five["m34"]))
    ax3.set_ylabel(r"$x_2/h$")
    ax3.set_title("five-point mask: atoms of $\\nu_w$\non $h\\mathbb{Z}^2\\setminus\\{0\\}$",
                  fontsize=16)

    b = np.linspace(-6.0, 6.0, 601)                       # omega c
    B1, B2 = np.meshgrid(b, b, indexing="ij")
    vs = a / (1 - a) ** 2
    logF = np.zeros_like(B1)
    for wi in (B1, B2):
        for m in range(1, 60):
            logF -= np.log1p(2 * vs * (1 - np.cos(q ** (-m) * (h / c) * wi)))
    Fgrid = np.exp(logF)
    rr = np.linspace(0, 6.0 * np.sqrt(2), 4000)
    Fmat = np.exp(-sum(np.log1p(q ** (-2 * i) * rr ** 2) for i in range(1, 60)))
    cs = ax2.contour(B1, B2, Fgrid, levels=list(levels), colors=BLUE, linewidths=1.2)
    ax2.clabel(cs, fmt="%.1f", fontsize=14)
    diag = np.diag(Fgrid)[300:]                           # along omega_1 = omega_2 >= 0
    inside = {}
    for lv in levels:
        radius = np.interp(-lv, -Fmat, rr)                # Fmat is decreasing in rr
        ax2.add_patch(plt.Circle((0, 0), radius, fill=False, ls=":", lw=0.9, color=GREY))
        # the solid level set crosses the diagonal at this distance from the origin
        inside[lv] = bool(np.sqrt(2) * np.interp(-lv, -diag, b[300:]) < radius)
    ax2.set_aspect("equal")
    ax2.set_xlim(-6, 6)
    ax2.set_ylim(-6, 6)
    ax2.set_xlabel(r"$\omega_1 c$")
    ax2.set_ylabel(r"$\omega_2 c$")
    ax2.set_title("level sets of $\\widehat{\\mu}_1$:\nframe (solid), Matérn (dotted)",
                  fontsize=16)
    fig.savefig(path, dpi=160)
    plt.close(fig)
    plt.rcParams.update(plt.rcParamsDefault)
    return {"a": float(a), "atoms_per_half_axis": int(len(pos)), "atom_at_rad": rad in set(pos),
            "diagonal_inside_circle": inside, "five_point_p": five["p"],
            "five_point_mass_5_0": five["m50"], "five_point_mass_3_4": five["m34"],
            "five_point_ratio_5_0_over_3_4": five["m50"] / five["m34"]}


def five_point_levy(t_over_h=1.0, d=2, tol=1e-16):
    """The Levy measure nu_w of the five-point resolvent mask kappa_t on h Z^2.

    By Proposition prop:resolvent-masks-exact(1) and (4), nu_w is the restriction to the nonzero
    lattice points of sum_k p^k/k sigma^{*k}, sigma the simple random walk step (mass 1/4 at each
    +-e_i) and p = 2d t^2/(h^2 + 2d t^2). The sum is cut where p^k/k < tol; the walk's law is
    computed exactly by repeated convolution on the box |n_i| <= K, which no k-step walk leaves.
    """
    p = 2 * d * t_over_h ** 2 / (1 + 2 * d * t_over_h ** 2)
    K = 1
    while p ** K / K >= tol:
        K += 1
    N = 2 * K + 1
    walk = np.zeros((N, N))
    walk[K, K] = 1.0
    nu = np.zeros((N, N))
    for k in range(1, K + 1):
        nxt = np.zeros_like(walk)
        nxt[1:, :] += walk[:-1, :]
        nxt[:-1, :] += walk[1:, :]
        nxt[:, 1:] += walk[:, :-1]
        nxt[:, :-1] += walk[:, 1:]
        walk = nxt / 4.0
        nu += p ** k / k * walk
    nu[K, K] = 0.0                                        # the restriction to the nonzero points
    return {"nu": nu, "K": K, "p": p, "m50": float(nu[K + 5, K]), "m34": float(nu[K + 3, K + 4])}


def main():
    FIG.mkdir(exist_ok=True)
    print("theory-strata.png", strata(FIG / "theory-strata.png"))
    print("theory-grid-steps.png", grid_steps(FIG / "theory-grid-steps.png"))
    print("theory-creation.png", creation(FIG / "theory-creation.png"))
    print("theory-frame.png", frame(FIG / "theory-frame.png"))


if __name__ == "__main__":
    main()
