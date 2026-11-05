"""Figure for Chapter 3: a contraction germ, its solution germ, and the shrinking of the germ.

The model (exposition §3, "An interactive look at a contraction germ").  W is the space of real
sequences w = (w_1, w_2, ...) with the sc-structure

    |w|_m^2 = sum_k e^{2 m k} |w_k|^2,      W_m = {w : |w|_m < infinity},

(the inclusions W_{m+1} -> W_m are compact because e^{2k} -> infinity, finite sequences are dense in
every W_m).  The parameter space is V = R with the partial quadrant C~ = [0, infinity).  Put

    B(a, w) = a w + beta(a),     beta(a)_k = a e^{-k/a}  (a > 0),   beta(0) = 0,

so that f(a, w) = w - B(a, w) is an sc^0-contraction germ: B(a, .) has Lipschitz constant |a| on every
level, which is <= eps for |a| < eps.  The solution germ is

    delta(a) = beta(a) / (1 - a),   |delta(a)|_m^2 = (a/(1-a))^2 q / (1 - q),   q = e^{2(m - 1/a)},

finite exactly for a < 1/m: the solution lies on level m only for parameters a < 1/m.  With the
germ of neighbourhoods N(m) = (-1/(m+2), 1/(m+2)) (so that B(a, .) is a 1/2-contraction and beta is
continuous into W_m on N(m) n C~), the proof of Theorem 3.33 certifies that delta is sc^k on the
shrunken germ N(m + s_k) n C~ with s_k = 2^k - 1 (exposition §3.5), i.e. on [0, 1/(m + 2^k + 1)).

Left: log10 |delta(a)|_m against a for m = 0, ..., 4; the curve for level m blows up at a = 1/m.
Right: for each level m (rows), the interval [0, 1/m) where delta(a) is in W_m at all (grey), the
germ N(m) n C~ of the contraction germ (k = 0), and the shrunken germs N(m + s_k) n C~ for k = 1, 2, 3.

Writes fig3-germ.png (150 dpi, 7 inches wide).  Run as a script to print the numbers quoted in the
text.
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np


def norm_delta(a, m):
    """|delta(a)|_m for 0 < a < 1 (infinity when a >= 1/m)."""
    a = np.asarray(a, dtype=float)
    out = np.full_like(a, np.inf)
    ok = (a > 0) & (a < 1) & ((m == 0) | (a * m < 1))
    q = np.exp(2.0 * (m - 1.0 / a[ok]))
    out[ok] = a[ok] / (1.0 - a[ok]) * np.sqrt(q / (1.0 - q))
    return out


def s(k):
    """The shift of Theorem 3.33 produced by the proof: s_0 = 0, s_{k+1} = 2 s_k + 1."""
    return 2 ** k - 1


def radius(m, k):
    """The radius of N(m + s_k): 1/(m + s_k + 2)."""
    return 1.0 / (m + s(k) + 2)


COLS = ["#08519c", "#3182bd", "#6baed6", "#9ecae1"]

fig = plt.figure(figsize=(7.0, 3.3))
gs = fig.add_gridspec(1, 2, width_ratios=[1.05, 1.0], wspace=0.32)
ax = fig.add_subplot(gs[0, 0])
bx = fig.add_subplot(gs[0, 1])

# ---------- left: the solution germ seen on the levels of W ----------
a = np.linspace(0.004, 0.74, 4000)
lev_cols = ["#000000", "#d62728", "#ff7f0e", "#2ca02c", "#9467bd"]
for m in range(5):
    with np.errstate(divide="ignore", invalid="ignore"):
        y = np.log10(norm_delta(a, m))
    y[~np.isfinite(y)] = np.nan
    ax.plot(a, y, color=lev_cols[m], lw=1.3, label=f"$m={m}$")
    if m >= 2:
        ax.axvline(1.0 / m, color=lev_cols[m], lw=0.6, ls=":")
ax.set_xlim(0, 0.74)
ax.set_ylim(-12, 3)
ax.set_xlabel("parameter $a\\in\\widetilde C=[0,\\infty)$")
ax.set_ylabel("$\\log_{10}|\\delta(a)|_m$")
ax.set_title("the solution germ on the levels $W_m$", fontsize=9)
ax.legend(fontsize=6.5, frameon=False, loc="lower right", ncol=2)
ax.text(0.505, 2.1, "$a=1/2$", fontsize=6.5, color=lev_cols[2])
ax.text(0.338, 2.1, "$1/3$", fontsize=6.5, color=lev_cols[3])
ax.text(0.255, 2.1, "$1/4$", fontsize=6.5, color=lev_cols[4])
for sp in ("top", "right"):
    ax.spines[sp].set_visible(False)

# ---------- right: the germs N(m + s_k) ----------
rows = range(6)
h = 0.16
for m in rows:
    y0 = 5 - m
    dom = 1.0 / m if m > 0 else 1.0
    bx.barh(y0 + 2 * h, min(dom, 0.62), height=h * 0.9, left=0, color="0.8", lw=0)
    for k in range(4):
        bx.barh(y0 + (1 - k) * h, radius(m, k), height=h * 0.9, left=0, color=COLS[k], lw=0,
                label=(f"$N(m+s_{k})$, $s_{k}={s(k)}$" if m == 0 else None))
handles, labels = bx.get_legend_handles_labels()
handles.insert(0, Patch(color="0.8"))
labels.insert(0, "$\\delta(a)\\in W_m$")
bx.set_yticks([5 - m + 0.08 for m in rows])
bx.set_yticklabels([f"$m={m}$" for m in rows], fontsize=7)
bx.set_xlim(0, 0.62)
bx.set_xlabel("$a$", labelpad=0)
bx.set_title("where $\\delta$ is certified sc$^k$: $N(m+2^k-1)\\cap\\widetilde C$", fontsize=9)
bx.legend(handles, labels, fontsize=6.0, frameon=False, loc="lower right")
for sp in ("top", "right", "left"):
    bx.spines[sp].set_visible(False)
bx.tick_params(axis="y", length=0)

fig.savefig("fig3-germ.png", dpi=150, bbox_inches="tight")

if __name__ == "__main__":
    for aa in (0.1, 0.2, 0.3):
        print(f"a={aa}: delta(a) in W_m exactly for m < 1/a = {1/aa:.2f}")
        for m in range(0, int(np.ceil(1 / aa))):
            print(f"   |delta({aa})|_{m} = {norm_delta(np.array([aa]), m)[0]:.3e}")
    for k in range(4):
        print(f"k={k}: s_k={s(k)}, radii of N(m+s_k) for m=0..3:",
              ", ".join(f"{radius(m, k):.4f}" for m in range(4)))
