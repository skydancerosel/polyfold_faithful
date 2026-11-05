// Interactive figure for Chapter 4: the fibres A_lam of a family over R near the corner of a
// quadrant (Theorem 4.23, Remark 4.24; the application of §10).  Plain JavaScript, no libraries.
// Finds the div with id "wavefront-figure" and draws a canvas with a slider for the parameter lam.
//
// The model (see fig4-wavefront.py): X = [0, inf)^2, g(x) = (x1 - 1)^2 + (x2 - 2)^2,
// A = {(g(x), x)}, A_lam = {x in X : g(x) = lam}: the part in the quadrant of the circle of radius
// sqrt(lam) around the source (1, 2).  The stratified critical values of p(lam, x) = lam are 0 (the
// source), 1 (tangent to the wall x1 = 0 at (0, 2)), 4 (tangent to the wall x2 = 0 at (1, 0)) and
// 5 (through the corner (0, 0), the corner stratum having dimension 0).
//
// Left: the room (white), the walls, the circle (dashed outside the room), A_lam (accent) with its
// endpoints on the walls.  Right (below on narrow screens): the neighbourhood of the special point of
// the nearest critical value, magnified nine times.  Bottom: the parameter line with the critical
// values and the number of components and endpoints of A_lam on each regular interval.
(function () {
  var root = document.getElementById("wavefront-figure");
  if (!root) return;

  function cssVar(name, fallback) {
    var v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    return v || fallback;
  }
  var FG = cssVar("--fg", "#222"), BG = cssVar("--bg", "#fff");
  var ACCENT = cssVar("--accent", "#c0392b"), MUTED = cssVar("--muted", "#888");

  var A = 1, B = 2, LMAX = 8.5, TOL = 0.005;
  var CRIT = [
    { v: 0, label: "source", pt: [1, 2] },
    { v: 1, label: "wall x₁=0", pt: [0, 2] },
    { v: 4, label: "wall x₂=0", pt: [1, 0] },
    { v: 5, label: "corner", pt: [0, 0] }
  ];

  root.style.maxWidth = "680px";
  root.style.fontFamily = "sans-serif";
  root.style.fontSize = "14px";
  root.style.color = FG;

  var canvas = document.createElement("canvas");
  canvas.style.width = "100%";
  canvas.style.display = "block";
  root.appendChild(canvas);

  var row = document.createElement("div");
  row.style.margin = "6px 0";
  var lab = document.createElement("label");
  lab.textContent = "λ ";
  var inp = document.createElement("input");
  inp.type = "range"; inp.min = 0; inp.max = LMAX; inp.step = 0.01; inp.value = 4.6;
  inp.style.width = "70%"; inp.style.verticalAlign = "middle";
  var out = document.createElement("span");
  out.style.marginLeft = "6px";
  row.appendChild(lab); row.appendChild(inp); row.appendChild(out);
  root.appendChild(row);

  var brow = document.createElement("div");
  brow.style.margin = "2px 0 6px 0";
  brow.appendChild(document.createTextNode("critical values: "));
  CRIT.forEach(function (c) {
    var b = document.createElement("button");
    b.textContent = String(c.v);
    b.style.marginRight = "6px";
    b.addEventListener("click", function () { inp.value = c.v; draw(); });
    brow.appendChild(b);
  });
  root.appendChild(brow);

  var info = document.createElement("div");
  info.style.lineHeight = "1.5";
  root.appendChild(info);

  inp.addEventListener("input", draw);
  window.addEventListener("resize", draw);

  // endpoints of A_lam on the walls: x2-values on x1 = 0, x1-values on x2 = 0 (positive ones)
  function wallPoints(lam) {
    var e1 = [], e2 = [];
    if (lam > A * A) { [-1, 1].forEach(function (s) { var y = B + s * Math.sqrt(lam - A * A); if (y > 0) e1.push(y); }); }
    if (lam > B * B) { [-1, 1].forEach(function (s) { var x = A + s * Math.sqrt(lam - B * B); if (x > 0) e2.push(x); }); }
    return [e1, e2];
  }

  function nearestCrit(lam) {
    var best = CRIT[0];
    CRIT.forEach(function (c) { if (Math.abs(c.v - lam) < Math.abs(best.v - lam)) best = c; });
    return best;
  }

  function status(lam) {
    var e = wallPoints(lam), n = e[0].length + e[1].length;
    var c = nearestCrit(lam);
    if (Math.abs(lam - c.v) < TOL) {
      if (c.v === 0) return { crit: true, text: "critical value 0: the interior critical point. A₀ is the single point (1, 2), of dimension 0, not 1." };
      if (c.v === 1) return { crit: true, text: "critical value 1: A₁ is tangent to the wall x₁ = 0 at (0, 2). There d_X = 1 but A₁ has no boundary point (d_A = 0): Theorem 4.22 (2) fails, A₁ is not in general position. Yet Dp ≠ 0 on A there: 1 is a regular value in the naive sense." };
      if (c.v === 4) return { crit: true, text: "critical value 4: A₄ is tangent to the wall x₂ = 0 at (1, 0): not in general position there, although Dp ≠ 0." };
      return { crit: true, text: "critical value 5: the circle passes through the corner, which is an isolated point of A₅ with d_X = 2 > dim A₅ (Remark 4.24 violated). Dp ≠ 0 there too: only the stratum of dimension 0 sees the corner." };
    }
    if (lam < TOL) return { crit: false, text: "Aλ is empty." };
    var comps = n === 0 ? 1 : n / 2;
    var txt = "regular value: Aλ is a compact 1-manifold with " + comps + (comps === 1 ? " component" : " components");
    if (n === 0) txt += ", a closed curve that misses the walls.";
    else txt += ", with " + e[0].length + " endpoint" + (e[0].length === 1 ? "" : "s") + " on x₁ = 0 and " + e[1].length + " on x₂ = 0, transversal to the walls, away from the corner.";
    return { crit: false, text: txt };
  }

  var ctx = canvas.getContext("2d");

  function view(x0, y0, w, h, win) {
    // equal-aspect map of the world window win = [xmin, xmax, ymin, ymax] into the box
    var sx = w / (win[1] - win[0]), sy = h / (win[3] - win[2]), s = Math.min(sx, sy);
    var ox = x0 + (w - s * (win[1] - win[0])) / 2, oy = y0 + (h - s * (win[3] - win[2])) / 2;
    return {
      X: function (x) { return ox + s * (x - win[0]); },
      Y: function (y) { return oy + s * (win[3] - y); },
      s: s, win: win, box: [ox, oy, s * (win[1] - win[0]), s * (win[3] - win[2])]
    };
  }

  function drawFibre(V, lam, lw) {
    var b = V.box, win = V.win;
    ctx.save();
    ctx.beginPath(); ctx.rect(b[0], b[1], b[2], b[3]); ctx.clip();
    // outside the room
    ctx.fillStyle = MUTED; ctx.globalAlpha = 0.18;
    ctx.fillRect(b[0], b[1], V.X(0) - b[0], b[3]);
    ctx.fillRect(V.X(0), V.Y(0), b[0] + b[2] - V.X(0), b[1] + b[3] - V.Y(0));
    ctx.globalAlpha = 1;
    // walls
    ctx.strokeStyle = FG; ctx.lineWidth = 1.6;
    ctx.beginPath(); ctx.moveTo(V.X(0), V.Y(win[3])); ctx.lineTo(V.X(0), V.Y(0)); ctx.lineTo(V.X(win[1]), V.Y(0)); ctx.stroke();
    if (lam > 0) {
      var r = Math.sqrt(lam), N = 1440, i, th, x, y, inside, prev = null;
      // dashed circle
      ctx.strokeStyle = MUTED; ctx.lineWidth = 0.8; ctx.setLineDash([3, 3]);
      ctx.beginPath();
      for (i = 0; i <= N; i++) {
        th = 2 * Math.PI * i / N; x = A + r * Math.cos(th); y = B + r * Math.sin(th);
        if (i === 0) ctx.moveTo(V.X(x), V.Y(y)); else ctx.lineTo(V.X(x), V.Y(y));
      }
      ctx.stroke(); ctx.setLineDash([]);
      // A_lam
      ctx.strokeStyle = ACCENT; ctx.lineWidth = lw;
      ctx.beginPath();
      for (i = 0; i <= N; i++) {
        th = 2 * Math.PI * i / N; x = A + r * Math.cos(th); y = B + r * Math.sin(th);
        inside = x >= -1e-9 && y >= -1e-9;
        if (inside && prev) ctx.lineTo(V.X(x), V.Y(y)); else if (inside) ctx.moveTo(V.X(x), V.Y(y));
        prev = inside;
      }
      ctx.stroke();
      var e = wallPoints(lam);
      ctx.fillStyle = ACCENT;
      e[0].forEach(function (yy) { ctx.beginPath(); ctx.arc(V.X(0), V.Y(yy), 3.5, 0, 2 * Math.PI); ctx.fill(); });
      e[1].forEach(function (xx) { ctx.beginPath(); ctx.arc(V.X(xx), V.Y(0), 3.5, 0, 2 * Math.PI); ctx.fill(); });
    }
    // the special point of a critical value
    var c = nearestCrit(lam);
    if (Math.abs(lam - c.v) < TOL) {
      ctx.strokeStyle = ACCENT; ctx.fillStyle = BG; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(V.X(c.pt[0]), V.Y(c.pt[1]), 5, 0, 2 * Math.PI); ctx.fill(); ctx.stroke();
    }
    // the source
    ctx.strokeStyle = FG; ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.moveTo(V.X(A) - 5, V.Y(B)); ctx.lineTo(V.X(A) + 5, V.Y(B));
    ctx.moveTo(V.X(A), V.Y(B) - 5); ctx.lineTo(V.X(A), V.Y(B) + 5);
    ctx.stroke();
    ctx.restore();
  }

  function draw() {
    var lam = parseFloat(inp.value);
    var W = Math.min(root.clientWidth || 680, 680);
    var wide = W >= 520;
    var mainH = wide ? Math.round(W * 0.6 * 1.0) : Math.round(W * 1.0);
    var zoomH = wide ? 0 : Math.round(W * 0.5);
    var stripH = 74;
    var H = mainH + zoomH + stripH + 10;
    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
    canvas.style.height = H + "px";
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = BG; ctx.fillRect(0, 0, W, H);
    ctx.font = "12px sans-serif";

    var mainWin = [-1.45, 3.45, -0.45, 4.45];
    var mw = wide ? W * 0.6 : W;
    var Vm = view(4, 18, mw - 8, mainH - 22, mainWin);
    drawFibre(Vm, lam, 2.4);
    ctx.fillStyle = FG;
    ctx.fillText("the room X = [0,∞)² and Aλ", Vm.box[0], 13);

    // magnified view around the special point of the nearest critical value
    var c = nearestCrit(lam), h = 0.27;
    var zWin = [c.pt[0] - h, c.pt[0] + h, c.pt[1] - h, c.pt[1] + h];
    var zx = wide ? mw + 8 : 4, zy = wide ? 30 : mainH + 18, zw = wide ? W - mw - 12 : W - 8, zh = wide ? mainH - 48 : zoomH - 22;
    var Vz = view(zx, zy, zw, zh, zWin);
    drawFibre(Vz, lam, 2.2);
    ctx.strokeStyle = MUTED; ctx.lineWidth = 0.8;
    ctx.strokeRect(Vz.box[0], Vz.box[1], Vz.box[2], Vz.box[3]);
    ctx.strokeRect(Vm.X(zWin[0]), Vm.Y(zWin[3]), Vm.X(zWin[1]) - Vm.X(zWin[0]), Vm.Y(zWin[2]) - Vm.Y(zWin[3]));
    ctx.fillStyle = MUTED;
    ctx.fillText("×9 near (" + c.pt[0] + ", " + c.pt[1] + ")", Vz.box[0], Vz.box[1] - 5);

    // the parameter line
    var y0 = H - 30, x0 = 16, x1 = W - 24;
    function PX(v) { return x0 + (x1 - x0) * v / LMAX; }
    ctx.strokeStyle = FG; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();
    ctx.fillStyle = FG; ctx.font = "11px sans-serif"; ctx.textAlign = "center";
    for (var t = 0; t <= 8; t++) {
      ctx.beginPath(); ctx.moveTo(PX(t), y0 - 3); ctx.lineTo(PX(t), y0 + 3); ctx.stroke();
      ctx.fillText(String(t), PX(t), y0 + 15);
    }
    ctx.fillText("λ", x1 + 12, y0 + 4);
    var edges = [0, 1, 4, 5, LMAX];
    for (var k = 0; k + 1 < edges.length; k++) {
      var mid = (edges[k] + edges[k + 1]) / 2, e = wallPoints(mid), n = e[0].length + e[1].length;
      var comps = n === 0 ? 1 : n / 2;
      ctx.fillStyle = MUTED;
      ctx.fillText(comps + "|" + n, PX(mid), y0 - 22);
    }
    ctx.textAlign = "left"; ctx.fillStyle = MUTED;
    ctx.fillText("components|ends:", x0, y0 - 36);
    ctx.textAlign = "center";
    CRIT.forEach(function (cc) {
      ctx.fillStyle = ACCENT;
      ctx.beginPath(); ctx.moveTo(PX(cc.v), y0 - 5); ctx.lineTo(PX(cc.v) + 5, y0); ctx.lineTo(PX(cc.v), y0 + 5); ctx.lineTo(PX(cc.v) - 5, y0); ctx.closePath(); ctx.fill();
    });
    ctx.strokeStyle = FG; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(PX(lam), y0 - 12); ctx.lineTo(PX(lam), y0 + 6); ctx.stroke();
    ctx.textAlign = "left";

    var st = status(lam);
    out.textContent = lam.toFixed(2) + "  (radius " + Math.sqrt(lam).toFixed(3) + " m, time " + (1000 * Math.sqrt(lam) / 343).toFixed(2) + " ms at 343 m/s)";
    info.innerHTML = "";
    var s = document.createElement("span");
    s.textContent = st.text;
    if (st.crit) s.style.color = ACCENT;
    info.appendChild(s);
  }

  draw();
})();
