"""Figure for Chapter 5: the solution set of f + lam*s for the two-wire section of the
application (Section 8).  f(x) = (x1^2 + x2^2)^2 - 2(x1^2 - x2^2), s = 1 near the solution sets.
Top: lam = -0.2 (regular), lam = 0 (critical: the figure eight, a node at the origin),
lam = 0.5 (regular).  The wall x1 = 0 bounds the half-plane X+ = {x1 >= 0}; the part of the
solution set in X+ is drawn in the accent colour, the rest dashed.  Bottom: the parameter line
with the critical values 0 and 1 and the solution sets on the regular intervals.
Writes fig5-perturb.png (150 dpi, 7 inches wide)."""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ACCENT, MUTED, FG = "#c0392b", "#888888", "#222222"
xx, yy = np.meshgrid(np.linspace(-1.75, 1.75, 1401), np.linspace(-0.85, 0.85, 681))
F = (xx**2 + yy**2)**2 - 2 * (xx**2 - yy**2)

fig = plt.figure(figsize=(7, 2.6))
gs = fig.add_gridspec(2, 3, height_ratios=[1.5, 0.75], hspace=0.12, wspace=0.08)
cases = [(-0.2, "λ = −0.2: regular"), (0.0, "λ = 0: critical (node)"), (0.5, "λ = 0.5: regular")]
for k, (lam, title) in enumerate(cases):
    ax = fig.add_subplot(gs[0, k])
    ax.axvspan(-1.75, 0, color="#eeeeee", zorder=0)
    ax.axvline(0, color=FG, lw=1.2, zorder=1)
    G = F + lam
    ax.contour(xx, yy, np.where(xx < 0, G, np.nan), levels=[0], colors=MUTED,
               linewidths=1.0, linestyles="dashed")
    ax.contour(xx, yy, np.where(xx >= 0, G, np.nan), levels=[0], colors=ACCENT, linewidths=2.0)
    if lam < 0:
        y0 = np.sqrt(np.sqrt(1 - lam) - 1)
        ax.plot([0, 0], [y0, -y0], "o", color=ACCENT, ms=4, zorder=3)
    if lam == 0:
        ax.plot([0], [0], "o", mfc="white", mec=ACCENT, ms=6, zorder=3)
    ax.plot([-1, 1], [0, 0], "x", color=FG, ms=5)
    ax.set_xlim(-1.75, 1.75); ax.set_ylim(-0.85, 0.85); ax.set_aspect("equal")
    ax.set_xticks([]); ax.set_yticks([])
    ax.set_title(title, fontsize=9)
    if k == 0:
        ax.text(-1.65, 0.68, "x₁ < 0", fontsize=7, color=MUTED)
        ax.text(0.08, 0.68, "X₊", fontsize=8, color=FG)

ax = fig.add_subplot(gs[1, :])
ax.set_xlim(-1.3, 1.6); ax.set_ylim(-1.2, 1.4)
ax.axhline(0, color=FG, lw=1)
for c in (0, 1):
    ax.plot([c], [0], "o", color=ACCENT, ms=6)
    ax.text(c, -0.55, str(c), ha="center", fontsize=8, color=ACCENT)
ax.text(-0.65, 0.35, "1 oval;  in X₊: 1 arc, 2 ends on the wall", ha="center", fontsize=7.5)
ax.text(0.5, 0.35, "2 ovals;  in X₊: 1 oval", ha="center", fontsize=7.5)
ax.text(1.3, 0.35, "empty", ha="center", fontsize=7.5)
ax.text(-1.28, -1.05, "parameter λ   (s = 1 near the solution set;  N(λs) = |λ|)", fontsize=7.5,
        color=MUTED)
ax.axis("off")
fig.savefig("fig5-perturb.png", dpi=150, bbox_inches="tight")
