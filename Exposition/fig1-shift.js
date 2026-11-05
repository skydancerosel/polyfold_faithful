// Interactive figure for Chapter 1: the shift map u -> u(. + R) on the line.
// Plain JavaScript, no libraries.  Finds the div with id "shift-figure" and draws a canvas with
// two sliders: the shift R and the regularity of u (a step, a tent, a smooth bump).  Below the
// canvas the three sizes ||u(.+R) - u||, ||u(.+R) - u - R u'|| (both in L^2) and the ratio of the
// first to R are printed, so that one sees what is differentiable into L^2 and what is not.
(function () {
  var root = document.getElementById("shift-figure");
  if (!root) return;

  function cssVar(name, fallback) {
    var v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    return v || fallback;
  }
  var FG = cssVar("--fg", "#222"), BG = cssVar("--bg", "#fff");
  var ACCENT = cssVar("--accent", "#c0392b"), MUTED = cssVar("--muted", "#888");

  root.style.maxWidth = "640px";
  root.style.fontFamily = "sans-serif";
  root.style.fontSize = "14px";
  root.style.color = FG;

  var canvas = document.createElement("canvas");
  canvas.style.width = "100%";
  canvas.style.display = "block";
  root.appendChild(canvas);

  function slider(label, min, max, step, value) {
    var row = document.createElement("div");
    row.style.margin = "4px 0";
    var lab = document.createElement("label");
    lab.textContent = label + " ";
    var inp = document.createElement("input");
    inp.type = "range"; inp.min = min; inp.max = max; inp.step = step; inp.value = value;
    inp.style.width = "55%"; inp.style.verticalAlign = "middle";
    var out = document.createElement("span");
    out.style.marginLeft = "6px";
    row.appendChild(lab); row.appendChild(inp); row.appendChild(out);
    root.appendChild(row);
    return { input: inp, out: out };
  }
  var sR = slider("shift R", 0.002, 0.5, 0.002, 0.2);
  var sU = slider("regularity of u (0 step, 1 tent, 2 smooth)", 0, 2, 1, 1);
  var info = document.createElement("div");
  info.style.marginTop = "6px"; info.style.lineHeight = "1.5";
  root.appendChild(info);

  // the three test functions and their derivatives (where they exist)
  var funcs = [
    { name: "step", u: function (s) { return (s >= 0 && s < 1) ? 1 : 0; }, du: null },
    { name: "tent", u: function (s) { return Math.max(0, 1 - Math.abs(s)); },
      du: function (s) { return Math.abs(s) < 1 ? -Math.sign(s) : 0; } },
    { name: "smooth bump", u: function (s) { return Math.exp(-s * s); },
      du: function (s) { return -2 * s * Math.exp(-s * s); } }
  ];

  var N = 8000, A = -3, B = 3, h = (B - A) / N;
  function l2(f) {
    var acc = 0;
    for (var i = 0; i < N; i++) { var v = f(A + i * h); acc += v * v; }
    return Math.sqrt(acc * h);
  }

  function draw() {
    var R = parseFloat(sR.input.value), k = parseInt(sU.input.value, 10), F = funcs[k];
    sR.out.textContent = R.toFixed(3);
    sU.out.textContent = F.name;
    var W = root.clientWidth || 360, H = Math.round(W * 0.5);
    var dpr = window.devicePixelRatio || 1;
    canvas.width = W * dpr; canvas.height = H * dpr; canvas.style.height = H + "px";
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = BG; ctx.fillRect(0, 0, W, H);
    var x0 = 28, x1 = W - 10, y0 = H - 24, y1 = 12;
    function X(s) { return x0 + (s - (-2.2)) / 4.4 * (x1 - x0); }
    function Y(v) { return y0 - v / 1.25 * (y0 - y1); }
    ctx.strokeStyle = MUTED; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();
    function curve(f, color, dash) {
      ctx.strokeStyle = color; ctx.lineWidth = 1.6; ctx.setLineDash(dash);
      ctx.beginPath();
      for (var i = 0; i <= 400; i++) {
        var s = -2.2 + 4.4 * i / 400, v = f(s);
        if (i === 0) ctx.moveTo(X(s), Y(v)); else ctx.lineTo(X(s), Y(v));
      }
      ctx.stroke(); ctx.setLineDash([]);
    }
    curve(F.u, FG, []);
    curve(function (s) { return F.u(s + R); }, ACCENT, [5, 4]);
    ctx.fillStyle = MUTED; ctx.font = "11px sans-serif";
    ctx.fillText("u (solid), u(. + R) (dashed)", x0 + 4, y1 + 10);
    ctx.fillText("s", x1 - 8, y0 + 16);

    var d0 = l2(function (s) { return F.u(s + R) - F.u(s); });
    var line = "||u(.+R) - u|| = " + d0.toFixed(4) + ",  divided by R: " + (d0 / R).toFixed(3);
    if (F.du) {
      var d1 = l2(function (s) { return F.u(s + R) - F.u(s) - R * F.du(s); });
      line += "<br>||u(.+R) - u - R u'|| = " + d1.toFixed(5) + ",  divided by R: " + (d1 / R).toFixed(4) +
        (k === 1 ? "  (= sqrt(2) R^{3/2}: o(R), so differentiable into L^2 at this point)"
                 : "  (O(R^2): differentiable into every level)");
    } else {
      line += "<br>no derivative: the quotient grows like R^{-1/2}; not differentiable into L^2";
    }
    info.innerHTML = line;
  }
  sR.input.addEventListener("input", draw);
  sU.input.addEventListener("input", draw);
  window.addEventListener("resize", draw);
  draw();
})();
