"""Figure for Chapter 1: the shift map loses one derivative.

Left: three functions on the line and their shifts by R = 0.3 (dashed): a step (in L^2 but not
in H^1), a tent (in H^1 but not in H^2) and a Gaussian (smooth).  The S^1 factor of the cylinder
R x S^1 is dropped; the computation is the same.

Right, on log-log axes: the L^2 size of what is left after the shift is approximated at the best
available order.  For the step, ||u(. + R) - u|| = sqrt(2R): no derivative exists, the shift is not
differentiable at u into L^2.  For the tent, ||u(. + R) - u - R u'|| = sqrt(2) R^{3/2}: the shift is
differentiable at u into L^2 (the remainder is o(R)), with derivative u', because u has one more
derivative than the target level asks for.  For the Gaussian the remainder is O(R^2).  Guide lines
of slopes 1/2, 3/2 and 2 are drawn.

Writes fig1-shift.png (150 dpi, 7 inches wide).
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

h = 1e-4                        # grid spacing; shifts are whole numbers of grid steps
s = np.arange(-4.0, 4.0, h)

step = ((s >= 0) & (s < 1)).astype(float)
tent = np.clip(1.0 - np.abs(s), 0.0, None)
tent_d = np.where(np.abs(s) < 1, -np.sign(s), 0.0)
gauss = np.exp(-s ** 2)
gauss_d = -2 * s * gauss


def shift(u, k):
    """u(. + R) with R = k h, k an integer: shift the array k places to the left."""
    return np.roll(u, -k)


def l2(u):
    return np.sqrt(np.sum(u ** 2) * h)


ks = np.unique(np.round(np.logspace(1, 3.3, 24)).astype(int))   # R from 1e-3 to 0.2
Rs = ks * h
rem_step = np.array([l2(shift(step, k) - step) for k in ks])
rem_tent = np.array([l2(shift(tent, k) - tent - R * tent_d) for k, R in zip(ks, Rs)])
rem_gauss = np.array([l2(shift(gauss, k) - gauss - R * gauss_d) for k, R in zip(ks, Rs)])

fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.0, 3.3), gridspec_kw={"width_ratios": [1.1, 1]})

# ---------- left: the functions and their shifts ----------
R0 = 0.3
k0 = int(round(R0 / h))
win = (s > -2.2) & (s < 2.2)
cols = {"step": "#1f77b4", "tent": "#d62728", "gauss": "#2ca02c"}
for name, u, off in (("step", step, 2.4), ("tent", tent, 1.2), ("gauss", gauss, 0.0)):
    ax.plot(s[win], u[win] + off, color=cols[name], lw=1.4)
    ax.plot(s[win], shift(u, k0)[win] + off, color=cols[name], lw=1.0, ls="--")
    ax.axhline(off, color="0.85", lw=0.6, zorder=0)
ax.text(-2.15, 2.4 + 0.95, "step: in $L^2$, not $H^1$", fontsize=8, color=cols["step"])
ax.text(-2.15, 1.2 + 0.95, "tent: in $H^1$, not $H^2$", fontsize=8, color=cols["tent"])
ax.text(-2.15, 0.0 + 0.95, "Gaussian: smooth", fontsize=8, color=cols["gauss"])
ax.set_yticks([])
ax.set_xlabel("$s$")
ax.set_title("$u$ (solid) and $u(\\cdot + R)$, $R = 0.3$ (dashed)", fontsize=9)
for sp in ("left", "right", "top"):
    ax.spines[sp].set_visible(False)

# ---------- right: remainders on log-log axes ----------
bx.loglog(Rs, rem_step, "o", ms=3, color=cols["step"], label="step: $\\|u(\\cdot+R)-u\\|$")
bx.loglog(Rs, rem_tent, "s", ms=3, color=cols["tent"], label="tent: $\\|u(\\cdot+R)-u-Ru'\\|$")
bx.loglog(Rs, rem_gauss, "^", ms=3, color=cols["gauss"], label="Gaussian: $\\|u(\\cdot+R)-u-Ru'\\|$")
rr = np.array([Rs[0], Rs[-1]])
bx.loglog(rr, np.sqrt(2 * rr), color=cols["step"], lw=0.7, alpha=0.6)
bx.loglog(rr, np.sqrt(2) * rr ** 1.5, color=cols["tent"], lw=0.7, alpha=0.6)
bx.loglog(rr, rem_gauss[-1] * (rr / Rs[-1]) ** 2, color=cols["gauss"], lw=0.7, alpha=0.6)
bx.text(0.0012, 0.11, "slope 1/2", fontsize=7, color=cols["step"])
bx.text(0.03, 0.0032, "slope 3/2", fontsize=7, color=cols["tent"])
bx.text(0.0012, 2.0e-6, "slope 2", fontsize=7, color=cols["gauss"])
bx.set_xlabel("$R$")
bx.set_ylabel("$L^2$ norm of the remainder")
bx.set_title("one level of regularity buys one order", fontsize=9)
bx.legend(fontsize=6.5, loc="lower right", frameon=False)
bx.grid(True, which="major", lw=0.3, alpha=0.5)

fig.tight_layout()
fig.savefig("fig1-shift.png", dpi=150)

# the exact values quoted in the text, as a check
if __name__ == "__main__":
    for k, R, a, b, c in zip(ks, Rs, rem_step, rem_tent, rem_gauss):
        print(f"R={R:.4f}  step {a:.5f} (sqrt(2R)={np.sqrt(2*R):.5f})  "
              f"tent {b:.6f} (sqrt2 R^1.5={np.sqrt(2)*R**1.5:.6f})  gauss {c:.3e} (ratio/R^2={c/R**2:.3f})")
