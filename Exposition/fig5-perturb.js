// Interactive figure for Chapter 5: the solution set of f + lam*s for the two-wire section of the
// application (Section 8).  Plain JavaScript, no libraries.  Finds the div with id
// "perturb-figure" and draws a canvas with a slider for the parameter lam.
//
// The model (see fig5-perturb.py): f(x) = (x1^2 + x2^2)^2 - 2(x1^2 - x2^2) = r1^2 r2^2 - 1, r1, r2
// the distances to the wires at (1, 0) and (-1, 0); s = 1 near the solution sets, N(lam*s) = |lam|.
// The zero set of f + lam is a Cassini oval.  Critical values: lam = 0 (the saddle of f at the
// origin: the figure eight) and lam = 1 (the minima of f at (+-1, 0): two points).  With the wall
// switched on, the space is the half-plane X+ = {x1 >= 0}; the restriction of f to the wall,
// f(0, x2) = x2^2 (x2^2 + 2), has the single critical value 0, so the critical values of the
// stratified problem are again 0 and 1.
(function () {
  var root = document.getElementById("perturb-figure");
  if (!root) return;

  function cssVar(name, fallback) {
    var v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    return v || fallback;
  }
  var FG = cssVar("--fg", "#222"), BG = cssVar("--bg", "#fff");
  var ACCENT = cssVar("--accent", "#c0392b"), MUTED = cssVar("--muted", "#888");

  var XMIN = -1.75, XMAX = 1.75, YMIN = -0.9, YMAX = 0.9, TOL = 0.006;
  function f(x, y) { var r2 = x * x + y * y; return r2 * r2 - 2 * (x * x - y * y); }

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
  inp.type = "range"; inp.min = -1.2; inp.max = 1.2; inp.step = 0.005; inp.value = -0.2;
  inp.style.width = "60%"; inp.style.verticalAlign = "middle";
  lab.appendChild(inp);
  var val = document.createElement("span");
  val.style.marginLeft = "6px";
  lab.appendChild(val);
  row.appendChild(lab);
  root.appendChild(row);

  var row2 = document.createElement("div");
  row2.style.margin = "4px 0";
  var wallBox = document.createElement("input");
  wallBox.type = "checkbox"; wallBox.checked = true; wallBox.id = "perturb-wall";
  var wallLab = document.createElement("label");
  wallLab.htmlFor = "perturb-wall";
  wallLab.textContent = " wall x₁ = 0 (space X₊ = {x₁ ≥ 0})  ";
  row2.appendChild(wallBox); row2.appendChild(wallLab);
  [0, 1].forEach(function (c) {
    var b = document.createElement("button");
    b.textContent = "λ = " + c;
    b.style.marginRight = "6px";
    b.onclick = function () { inp.value = c; draw(); };
    row2.appendChild(b);
  });
  root.appendChild(row2);

  var status = document.createElement("div");
  status.style.minHeight = "3.2em";
  status.style.lineHeight = "1.35";
  root.appendChild(status);

  // Marching squares on an n-by-m grid: returns segments [x0, y0, x1, y1].
  function zeroSegments(lam, n, m) {
    var segs = [], hx = (XMAX - XMIN) / n, hy = (YMAX - YMIN) / m, i, j;
    var v = [];
    for (j = 0; j <= m; j++) {
      v.push([]);
      for (i = 0; i <= n; i++) v[j].push(f(XMIN + i * hx, YMIN + j * hy) + lam);
    }
    function interp(xa, ya, va, xb, yb, vb) {
      var t = va / (va - vb);
      return [xa + t * (xb - xa), ya + t * (yb - ya)];
    }
    for (j = 0; j < m; j++) {
      for (i = 0; i < n; i++) {
        var x0 = XMIN + i * hx, y0 = YMIN + j * hy, x1 = x0 + hx, y1 = y0 + hy;
        var c = [[x0, y0, v[j][i]], [x1, y0, v[j][i + 1]], [x1, y1, v[j + 1][i + 1]],
                 [x0, y1, v[j + 1][i]]];
        var pts = [];
        for (var e = 0; e < 4; e++) {
          var a = c[e], b = c[(e + 1) % 4];
          if ((a[2] >= 0) !== (b[2] >= 0)) pts.push(interp(a[0], a[1], a[2], b[0], b[1], b[2]));
        }
        if (pts.length === 2) {
          segs.push([pts[0][0], pts[0][1], pts[1][0], pts[1][1]]);
        } else if (pts.length === 4) {
          var center = f((x0 + x1) / 2, (y0 + y1) / 2) + lam;
          var pos0 = c[0][2] >= 0;
          if ((center >= 0) === pos0) {
            segs.push([pts[0][0], pts[0][1], pts[1][0], pts[1][1]]);
            segs.push([pts[2][0], pts[2][1], pts[3][0], pts[3][1]]);
          } else {
            segs.push([pts[0][0], pts[0][1], pts[3][0], pts[3][1]]);
            segs.push([pts[1][0], pts[1][1], pts[2][0], pts[2][1]]);
          }
        }
      }
    }
    return segs;
  }

  function describe(lam, wall) {
    var allow = Math.abs(lam) <= 1 ? "allowable (N(λs) = " + Math.abs(lam).toFixed(3) + " ≤ 1)"
                                   : "not allowable (N(λs) = " + Math.abs(lam).toFixed(3) + " > 1)";
    var s;
    if (Math.abs(lam) < TOL) {
      s = "<b>critical</b>: the figure eight; f′(0) = 0 at the node, not a manifold there.";
      if (wall) s += " The node lies on the wall: (f, 0) is not in good position, and a" +
        " perturbation vanishing near the wall cannot remove it.";
    } else if (Math.abs(lam - 1) < TOL) {
      s = "<b>critical</b>: the minima (±1, 0) of f, isolated points.";
    } else if (lam > 1) {
      s = "regular (vacuously): the solution set is empty.";
    } else if (lam < 0) {
      var y0 = Math.sqrt(Math.sqrt(1 - lam) - 1);
      s = "regular: one oval, a compact 1-manifold.";
      if (wall) s += " In X₊: one arc with ends (0, ±" + y0.toFixed(3) + ") on the wall," +
        " crossing it transversally (general position).";
    } else {
      s = "regular: two ovals, a compact 1-manifold.";
      if (wall) s += " In X₊: one oval, away from the wall.";
    }
    return s + "<br><span style='color:" + MUTED + "'>Perturbation λs: " + allow + ".</span>";
  }

  function draw() {
    var lam = parseFloat(inp.value), wall = wallBox.checked;
    val.textContent = lam.toFixed(3);
    var dpr = window.devicePixelRatio || 1;
    var W = Math.max(240, Math.min(680, root.clientWidth || 680));
    var H = Math.round(W * (YMAX - YMIN) / (XMAX - XMIN));
    canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
    canvas.style.height = H + "px";
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = BG; ctx.fillRect(0, 0, W, H);
    function px(x) { return (x - XMIN) / (XMAX - XMIN) * W; }
    function py(y) { return (YMAX - y) / (YMAX - YMIN) * H; }

    if (wall) {
      ctx.globalAlpha = 0.12; ctx.fillStyle = MUTED;
      ctx.fillRect(0, 0, px(0), H); ctx.globalAlpha = 1;
      ctx.strokeStyle = FG; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.moveTo(px(0), 0); ctx.lineTo(px(0), H); ctx.stroke();
    }
    ctx.strokeStyle = MUTED; ctx.lineWidth = 0.6;
    ctx.strokeRect(0.5, 0.5, W - 1, H - 1);

    var segs = zeroSegments(lam, 280, 144);
    segs.forEach(function (s) {
      var inside = !wall || (s[0] + s[2]) / 2 >= 0;
      ctx.strokeStyle = inside ? ACCENT : MUTED;
      ctx.lineWidth = inside ? 2.4 : 1.2;
      ctx.setLineDash(inside ? [] : [4, 3]);
      ctx.beginPath(); ctx.moveTo(px(s[0]), py(s[1])); ctx.lineTo(px(s[2]), py(s[3])); ctx.stroke();
    });
    ctx.setLineDash([]);
    if (Math.abs(lam - 1) < TOL) {
      [-1, 1].forEach(function (x) {
        if (wall && x < 0) return;
        ctx.fillStyle = ACCENT; ctx.beginPath(); ctx.arc(px(x), py(0), 4, 0, 2 * Math.PI); ctx.fill();
      });
    }
    if (wall && lam < -TOL) {
      var y0 = Math.sqrt(Math.sqrt(1 - lam) - 1);
      [y0, -y0].forEach(function (y) {
        ctx.fillStyle = ACCENT; ctx.beginPath(); ctx.arc(px(0), py(y), 3.5, 0, 2 * Math.PI); ctx.fill();
      });
    }
    // the wires
    ctx.strokeStyle = FG; ctx.lineWidth = 1.5;
    [-1, 1].forEach(function (x) {
      ctx.beginPath();
      ctx.moveTo(px(x) - 4, py(0) - 4); ctx.lineTo(px(x) + 4, py(0) + 4);
      ctx.moveTo(px(x) - 4, py(0) + 4); ctx.lineTo(px(x) + 4, py(0) - 4);
      ctx.stroke();
    });
    status.innerHTML = describe(lam, wall);
  }

  inp.addEventListener("input", draw);
  wallBox.addEventListener("change", draw);
  window.addEventListener("resize", draw);
  draw();
})();
