"""Figure for Chapter 4: the fibres A_lam of a family over R near the corner of a quadrant.

The model (exposition §10, "Application: a wavefront in the corner of a room", and the figure in §8).
X = [0, inf)^2 (in the exposition times a passenger sc-Banach space W, which does not change the
picture), Z = R x X, and

    g(x) = (x1 - a)^2 + (x2 - b)^2,   a = 1, b = 2,
    A = {(g(x), x) : x in X, g(x) < 9},     A_lam = {x in X : g(x) = lam},

the part inside the quadrant of the circle of radius r = sqrt(lam) around the source (a, b).  The
stratified critical values of the projection p : A -> R, (lam, x) -> lam, are

    0  (interior stratum: grad g = 0 at the source),
    1 = a^2  (edge stratum x1 = 0: the circle is tangent to the wall x1 = 0 at (0, 2)),
    4 = b^2  (edge stratum x2 = 0: tangent to the wall x2 = 0 at (1, 0)),
    5 = a^2 + b^2  (corner stratum, of dimension 0: the circle passes through the corner (0, 0)).

Between them A_lam is a compact 1-manifold with boundary on the walls and away from the corner:
a closed curve (0 < lam < 1), one arc with both ends on x1 = 0 (1 < lam < 4), two arcs, the small
one cutting off the corner (4 < lam < 5), one arc from wall to wall (lam > 5).

Top: three fibres, lam = 4 (critical: tangent to the wall x2 = 0), lam = 4.6 (regular: the small
arc cuts off the corner transversally), lam = 5 (critical: the corner is an isolated point of A_5);
the grey box of each is magnified nine times below it (around the point of tangency (1, 0) for
lam = 4, around the corner for the others).  Bottom: the parameter line with the four stratified
critical values and the number of components and of boundary points of A_lam on each regular
interval.

Writes fig4-wavefront.png (150 dpi, 7 inches wide) next to this script.  Run as a script to print
the numbers quoted in the text.
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

A_, B_ = 1.0, 2.0
CRIT = [(0.0, "source"), (1.0, "wall $x_1=0$"), (4.0, "wall $x_2=0$"), (5.0, "corner")]
FG, ACC, MUT = "#222222", "#c0392b", "#888888"


def wall_points(lam):
    """Endpoints of A_lam on the walls (x1 = 0 and x2 = 0), with x2 > 0 resp. x1 > 0."""
    e1 = [B_ + s * np.sqrt(lam - A_ ** 2) for s in (-1, 1)] if lam > A_ ** 2 else []
    e2 = [A_ + s * np.sqrt(lam - B_ ** 2) for s in (-1, 1)] if lam > B_ ** 2 else []
    return [y for y in e1 if y > 0], [x for x in e2 if x > 0]


def topology(lam):
    """(components, endpoints on x1 = 0, endpoints on x2 = 0) for a regular value lam > 0."""
    e1, e2 = wall_points(lam)
    if not e1 and not e2:
        return 1, 0, 0
    comps = (len(e1) + len(e2)) // 2
    return comps, len(e1), len(e2)


def draw_fibre(ax, lam, lim, lw=1.6):
    r = np.sqrt(lam)
    th = np.linspace(0, 2 * np.pi, 4001)
    x, y = A_ + r * np.cos(th), B_ + r * np.sin(th)
    ins = (x >= -1e-12) & (y >= -1e-12)
    ax.plot(x, y, color=MUT, lw=0.7, ls=(0, (2, 2)))
    xi, yi = x.copy(), y.copy()
    xi[~ins], yi[~ins] = np.nan, np.nan
    ax.plot(xi, yi, color=ACC, lw=lw)
    e1, e2 = wall_points(lam)
    ax.plot([0] * len(e1), e1, "o", color=ACC, ms=3.2)
    ax.plot(e2, [0] * len(e2), "o", color=ACC, ms=3.2)
    # walls and the room
    ax.fill_between([lim[0], 0], lim[2], lim[3], color="0.92", lw=0)
    ax.fill_between([0, lim[1]], lim[2], 0, color="0.92", lw=0)
    ax.plot([0, 0], [0, lim[3]], color=FG, lw=1.2)
    ax.plot([0, lim[1]], [0, 0], color=FG, lw=1.2)
    ax.set_xlim(lim[0], lim[1])
    ax.set_ylim(lim[2], lim[3])
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for sp in ax.spines.values():
        sp.set_visible(False)


fig = plt.figure(figsize=(7.0, 4.7))
gs = fig.add_gridspec(3, 3, height_ratios=[2.6, 1.25, 0.75], hspace=0.12, wspace=0.08)
panels = [(4.0, "$\\lambda=4$: critical (tangent)", (0.73, 1.27, -0.12, 0.42), "near $(1,0)$"),
          (4.6, "$\\lambda=4.6$: regular", (-0.12, 0.42, -0.12, 0.42), "near the corner"),
          (5.0, "$\\lambda=5$: critical (corner)", (-0.12, 0.42, -0.12, 0.42), "near the corner")]
for j, (lam, title, zlim, zlab) in enumerate(panels):
    ax = fig.add_subplot(gs[0, j])
    draw_fibre(ax, lam, (-1.45, 3.45, -0.45, 4.45))
    ax.plot([A_], [B_], "+", color=FG, ms=6)
    ax.set_title(title, fontsize=7.5)
    if j == 0:
        ax.text(A_ + 0.08, B_ + 0.12, "source", fontsize=6.5, color=FG)
        ax.text(0.06, 4.15, "$x_1=0$", fontsize=6.5, color=FG)
        ax.text(2.55, 0.08, "$x_2=0$", fontsize=6.5, color=FG)
    special = {4.0: (A_, 0.0), 5.0: (0.0, 0.0)}
    if lam in special:
        ax.plot(*special[lam], "o", color=ACC, ms=4.5, mfc="white", mew=1.4)
    # second row: the box of the first row, magnified
    zx = fig.add_subplot(gs[1, j])
    draw_fibre(zx, lam, zlim, lw=1.4)
    if lam in special:
        zx.plot(*special[lam], "o", color=ACC, ms=5, mfc="white", mew=1.4)
    for sp in zx.spines.values():
        sp.set_visible(True)
        sp.set_color(MUT)
        sp.set_linewidth(0.6)
    zx.set_title(f"$\\times 9$, {zlab}", fontsize=6.5, color=MUT, pad=2)
    ax.add_patch(plt.Rectangle((zlim[0], zlim[2]), zlim[1] - zlim[0], zlim[3] - zlim[2],
                               fill=False, edgecolor=MUT, lw=0.6))

# bottom: the parameter line
bx = fig.add_subplot(gs[2, :])
L = 8.5
bx.plot([-0.3, L], [0, 0], color=FG, lw=0.9)
for t in range(0, 9):
    bx.plot([t, t], [-0.06, 0.06], color=FG, lw=0.7)
    bx.text(t, -0.42, str(t), ha="center", fontsize=6.5)
for v, lab in CRIT:
    bx.plot([v], [0], "D", color=ACC, ms=5)
    bx.text(v, 0.22, lab, ha="center", fontsize=6.3, color=ACC)
edges = [0.0, 1.0, 4.0, 5.0, L]
for lo, hi in zip(edges[:-1], edges[1:]):
    c, n1, n2 = topology(0.5 * (lo + hi))
    txt = f"{c} comp., {n1 + n2} ends" if hi - lo > 0.9 else f"{c}, {n1 + n2}"
    bx.text(0.5 * (lo + hi), 0.62, txt, ha="center", fontsize=6.3, color=FG)
bx.text(L + 0.15, -0.05, "$\\lambda$", fontsize=8)
bx.set_xlim(-0.4, L + 0.5)
bx.set_ylim(-0.6, 0.9)
bx.axis("off")

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig4-wavefront.png")
fig.savefig(out, dpi=150, bbox_inches="tight")

if __name__ == "__main__":
    for v, lab in CRIT:
        print(f"critical value {v} ({lab.replace('$', '')}), r = {np.sqrt(v):.4f}, "
              f"t = {1000 * np.sqrt(v) / 343:.2f} ms at c = 343 m/s")
    for lam in (0.5, 2.0, 4.6, 6.0):
        c, n1, n2 = topology(lam)
        e1, e2 = wall_points(lam)
        print(f"lam = {lam}: {c} component(s), ends on x1=0 at x2 = {np.round(e1, 3).tolist()}, "
              f"on x2=0 at x1 = {np.round(e2, 3).tolist()}")
