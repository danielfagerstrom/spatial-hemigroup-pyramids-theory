# /// script
# requires-python = ">=3.10"
# dependencies = ["numpy", "mpmath"]
# ///
# Copied from spatial-hemigroup-scale-space, scripts/sampled_gaussian_increments.py (Q-0630);
# the print of the site of the least coefficient was added for the paper's text (review r1, R11).
# The Gaussian is sampled at the 4096 sites n = -2048, ..., 2047 and renormalized there; the ring
# is the periodic grid of those sites.
#
# Review r2 (section 4): in double precision the least coefficient of the pair (0.7, 3.0) is
# rounding. Part 2 recomputes that pair on the same periodic grid at 60 digits. Part 3 computes the
# fourth-moment certificate for the pair (0.5, 0.6) on the infinite lattice Z: with X and Z the
# normalized samples at widths 0.5 and 0.6, a probability step Y (integer valued, independent of X,
# Z = X + Y in law) would have E Y^2 = E Z^2 - E X^2 and E Y^4 = E Z^4 - E X^4 - 6 E X^2 E Y^2,
# and E Y^4 >= E Y^2 on the integers. The script prints both sides and a bound for the tails it
# omits.
#
#     uv run scripts/sampled_gaussian_increments.py
import numpy as np
import mpmath as mp

# Part 1: double precision, four pairs.
N = 4096; n = np.arange(-N // 2, N // 2)
def sg(s):
    k = np.exp(-n**2 / (2 * s * s)); return k / k.sum()
for s, t in [(1.0, 1.2), (2.0, 2.5), (0.7, 3.0), (0.5, 0.6)]:
    Fs = np.fft.fft(np.fft.ifftshift(sg(s))); Ft = np.fft.fft(np.fft.ifftshift(sg(t)))
    inc = np.fft.fftshift(np.fft.ifft(Ft / Fs).real)
    print(s, t, "min increment coeff:", inc.min(), "at n =", abs(int(n[inc.argmin()])),
          "max:", inc.max(), "sum:", inc.sum())

# Part 2: the pair (0.7, 3.0) at 60 digits, same periodic grid, sites |m| <= 60.
mp.mp.dps = 60
C = [mp.cos(2 * mp.pi * j / N) for j in range(N)]
def transfer(sig):
    sig = mp.mpf(sig); w = {}
    for k in range(0, N // 2 + 1):
        v = mp.e ** (-mp.mpf(k) ** 2 / (2 * sig * sig))
        if v < mp.mpf(10) ** (-(mp.mp.dps + 20)):
            break
        w[k] = v
    tot = w[0] + 2 * sum(w[k] for k in w if k > 0)
    return [(w[0] + sum(2 * w[k] * C[(j * k) % N] for k in w if k > 0)) / tot
            for j in range(N // 2 + 1)]
Fs = transfer('0.7'); Ft = transfer('3.0')
R = [Ft[j] / Fs[j] for j in range(N // 2 + 1)]
coef = []
for m in range(0, 61):
    acc = R[0] + R[N // 2] * C[(m * (N // 2)) % N]
    acc += sum(2 * R[j] * C[(j * m) % N] for j in range(1, N // 2))
    coef.append(acc / N)
m0 = min(range(61), key=lambda m: coef[m])
print("0.7 3.0 at 60 digits: least coefficient", mp.nstr(coef[m0], 6), "at n =", m0)

# Part 3: the fourth-moment certificate for (0.5, 0.6) on Z, sums over |k| <= 5.
def moments(sig, K=5):
    sig = mp.mpf(sig); ks = range(-K, K + 1)
    w = [mp.e ** (-mp.mpf(k) ** 2 / (2 * sig * sig)) for k in ks]
    Zs = sum(w)
    return (sum(wi * k**2 for wi, k in zip(w, ks)) / Zs,
            sum(wi * k**4 for wi, k in zip(w, ks)) / Zs)
x2, x4 = moments('0.5'); z2, z4 = moments('0.6')
y2 = z2 - x2; y4 = z4 - x4 - 6 * x2 * y2
tail = 2 * sum(mp.mpf(k) ** 4 * mp.e ** (-mp.mpf(k) ** 2 / (2 * mp.mpf('0.6') ** 2))
               for k in range(6, 200))
print("0.5 0.6 on Z: E Y^2 =", mp.nstr(y2, 6), " E Y^4 =", mp.nstr(y4, 6),
      " omitted fourth-moment tail <", mp.nstr(tail, 2))
