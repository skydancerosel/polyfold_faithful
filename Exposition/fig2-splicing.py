"""Figure for Chapter 2: a retract whose dimension jumps (2010 paper, Example 1.22).

On R + L^2(R) with the sc-structure E_m = H^{m,delta_m}(R), let beta be a smooth bump of L^2-norm one
supported in [-1, 1], beta_t = beta(. + e^{1/t}) for t > 0 (a copy of beta centred at s = -e^{1/t}),
pi_t f = <f, beta_t> beta_t for t > 0 and pi_t = 0 for t <= 0.  Then r(t, f) = (t, pi_t f) is an
sc-smooth retraction and its image O is a half-line (t <= 0) glued to a half-plane (t > 0).

Left: O in the coordinates (t, sigma), sigma = <f, beta_t>; the fibre dimension jumps from 0 to 1.
Right, top: the bumps beta_t for four values of t; as t -> 0+ the bump runs off to -infinity.
Right, bottom: the bound  e^{-Delta e^{1/t}} / t  on the difference quotient |pi_t f|_m / t for f one
level up (Delta = delta_{m+1} - delta_m), for Delta = 0.1 and 0.3, against the single-level bound 1/t
(Delta = 0).  The former is flat to every order at t = 0; the latter blows up.

Writes fig2-splicing.png (150 dpi, 7 inches wide).
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def bump(s):
    """A smooth bump supported in [-1, 1], normalized to L^2-norm one on a fine grid."""
    out = np.zeros_like(s)
    inside = np.abs(s) < 1
    out[inside] = np.exp(-1.0 / (1.0 - s[inside] ** 2))
    return out


# normalization constant of the bump
_s = np.linspace(-1, 1, 20001)
_b = bump(_s)
NORM = np.sqrt(np.trapezoid(_b ** 2, _s)) if hasattr(np, "trapezoid") else np.sqrt(np.trapz(_b ** 2, _s))


def beta_t(s, t):
    return bump(s + np.exp(1.0 / t)) / NORM


fig = plt.figure(figsize=(7.0, 3.6))
gs = fig.add_gridspec(2, 2, width_ratios=[1.0, 1.15], height_ratios=[1, 1], hspace=0.55, wspace=0.3)
ax = fig.add_subplot(gs[:, 0])
bx = fig.add_subplot(gs[0, 1])
cx = fig.add_subplot(gs[1, 1])

# ---------- left: the retract in the (t, sigma) plane ----------
ax.fill_between([0, 1.1], -1.3, 1.3, color="#9ecae1", alpha=0.6, lw=0)
ax.plot([-1.1, 0], [0, 0], color="#08519c", lw=2.5, solid_capstyle="round")
ax.plot([0, 1.1], [0, 0], color="#08519c", lw=0.8, ls=":")
ax.plot([0], [0], "o", color="#08519c", ms=4)
ax.set_xlim(-1.1, 1.1)
ax.set_ylim(-1.3, 1.3)
ax.set_xlabel("$t$")
ax.set_ylabel(r"$\sigma = \langle f, \beta_t\rangle$")
ax.text(-1.0, 0.18, "fibre dimension 0", fontsize=8, color="#08519c")
ax.text(0.12, 1.0, "fibre dimension 1", fontsize=8, color="#08519c")
ax.text(0.12, -1.2, r"$O = \{(t,\sigma\,\beta_t)\}$", fontsize=8)
ax.set_title(r"the retract $O = r(\mathbb{R}\oplus E)$", fontsize=9)
for sp in ("top", "right"):
    ax.spines[sp].set_visible(False)

# ---------- right, top: the sliding bump ----------
s = np.linspace(-20, 1.5, 4000)
ts = [1.0, 0.6, 0.45, 0.36]
cols = ["#d62728", "#ff7f0e", "#2ca02c", "#9467bd"]
for t, c in zip(ts, cols):
    bx.plot(s, beta_t(s, t), color=c, lw=1.2, label=f"$t={t}$")
bx.set_xlim(-20, 1.5)
bx.set_yticks([])
bx.set_xlabel("$s$", labelpad=0)
bx.set_title(r"$\beta_t = \beta(\cdot + e^{1/t})$ runs to $-\infty$", fontsize=9)
bx.legend(fontsize=6.5, frameon=False, loc="upper left", ncol=2)
for sp in ("top", "right", "left"):
    bx.spines[sp].set_visible(False)

# ---------- right, bottom: the difference-quotient bound ----------
t = np.linspace(0.02, 1.0, 600)
with np.errstate(over="ignore"):
    cx.plot(t, 1.0 / t, color="0.4", lw=1.0, ls="--", label=r"$\Delta = 0$: $1/t$")
    for d, c in ((0.1, "#1f77b4"), (0.3, "#08519c")):
        cx.plot(t, np.exp(-d * np.exp(1.0 / t)) / t, color=c, lw=1.4, label=rf"$\Delta = {d}$")
cx.set_ylim(0, 3.2)
cx.set_xlim(0, 1)
cx.set_xlabel("$t$", labelpad=0)
cx.set_ylabel(r"$e^{-\Delta e^{1/t}}/t$", fontsize=8)
cx.set_title("the quotient bound: flat at $t = 0$ one level up", fontsize=9)
cx.legend(fontsize=6.5, frameon=False, loc="upper right")
for sp in ("top", "right"):
    cx.spines[sp].set_visible(False)

fig.savefig("fig2-splicing.png", dpi=150, bbox_inches="tight")

if __name__ == "__main__":
    # the numbers quoted in the text, as a check
    for tt in ts:
        print(f"t={tt}: bump centred at s=-e^(1/t)={-np.exp(1/tt):.2f}")
    for a in (0.5, 0.25, 0.1):
        print(f"|a|={a}: gluing length R=e^(1/|a|)-e={np.exp(1/a)-np.e:.2f}")
    for tt in (0.5, 0.3, 0.2):
        print(f"t={tt}: e^(-0.1 e^(1/t))/t={np.exp(-0.1*np.exp(1/tt))/tt:.3e},  1/t={1/tt:.2f}")
