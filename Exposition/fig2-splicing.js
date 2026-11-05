// Interactive figure for Chapter 2: a retract whose dimension jumps (the toy splicing of the 2010
// paper, Example 1.22).  Plain JavaScript, no libraries.  Finds the div with id "splicing-figure" and
// draws a canvas with one slider, the parameter t.  Left: the retract O, a half-line {t <= 0} glued to a
// half-plane {t > 0}, with the current t marked and the current fibre drawn.  Right: the bump
// beta_t = beta(. + e^{1/t}) sliding to -infinity as t -> 0+, together with a fixed test function f.
// Below: the coefficient <f, beta_t>, the position -e^{1/t} of the bump, and the bound
// e^{-Delta e^{1/t}}/t on the difference quotient one level up (Delta = 0.1), against 1/t on one level.
(function () {
  var root = document.getElementById("splicing-figure");
  if (!root) return;

  function cssVar(name, fallback) {
    var v = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
    return v || fallback;
  }
  var FG = cssVar("--fg", "#222"), BG = cssVar("--bg", "#fff");
  var ACCENT = cssVar("--accent", "#c0392b"), MUTED = cssVar("--muted", "#888");

  root.style.maxWidth = "680px";
  root.style.fontFamily = "sans-serif";
  root.style.fontSize = "14px";
  root.style.color = FG;

  var canvas = document.createElement("canvas");
  canvas.style.width = "100%";
  canvas.style.display = "block";
  root.appendChild(canvas);

  var row = document.createElement("div");
  row.style.margin = "4px 0";
  var lab = document.createElement("label");
  lab.textContent = "parameter t ";
  var inp = document.createElement("input");
  inp.type = "range"; inp.min = -1; inp.max = 1; inp.step = 0.01; inp.value = 0.5;
  inp.style.width = "55%"; inp.style.verticalAlign = "middle";
  var out = document.createElement("span");
  out.style.marginLeft = "6px";
  row.appendChild(lab); row.appendChild(inp); row.appendChild(out);
  root.appendChild(row);
  var info = document.createElement("div");
  info.style.marginTop = "6px"; info.style.lineHeight = "1.5";
  root.appendChild(info);

  // the bump beta, supported in [-1, 1], normalized to L^2-norm one
  function bump0(s) { return Math.abs(s) < 1 ? Math.exp(-1 / (1 - s * s)) : 0; }
  var N = 4000, h = 2 / N, acc = 0;
  for (var i = 0; i < N; i++) { var v = bump0(-1 + i * h); acc += v * v; }
  var NORM = Math.sqrt(acc * h);
  function beta(s) { return bump0(s) / NORM; }
  // the fixed test function f: a Gaussian centred at s = -4 (so that <f, beta_t> is visible for t ~ 1)
  function f(s) { return Math.exp(-(s + 4) * (s + 4) / 2); }

  function draw() {
    var t = parseFloat(inp.value);
    out.textContent = t.toFixed(2);
    var W = root.clientWidth || 360, H = Math.round(W * 0.5);
    var dpr = window.devicePixelRatio || 1;
    canvas.width = W * dpr; canvas.height = H * dpr; canvas.style.height = H + "px";
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = BG; ctx.fillRect(0, 0, W, H);
    var half = Math.floor(W / 2);

    // ---- left panel: the retract in the (t, sigma) plane ----
    var x0 = 10, x1 = half - 12, y0 = H - 22, y1 = 12;
    function X(tt) { return x0 + (tt + 1) / 2 * (x1 - x0); }
    function Y(sg) { return (y0 + y1) / 2 - sg / 1.3 * (y0 - y1) / 2; }
    ctx.fillStyle = MUTED; ctx.globalAlpha = 0.25;
    ctx.fillRect(X(0), y1, X(1) - X(0), y0 - y1);
    ctx.globalAlpha = 1;
    ctx.strokeStyle = FG; ctx.lineWidth = 2.5;
    ctx.beginPath(); ctx.moveTo(X(-1), Y(0)); ctx.lineTo(X(0), Y(0)); ctx.stroke();
    ctx.strokeStyle = MUTED; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();
    // the current fibre
    ctx.strokeStyle = ACCENT; ctx.lineWidth = 1.5;
    if (t > 0) { ctx.beginPath(); ctx.moveTo(X(t), y1); ctx.lineTo(X(t), y0); ctx.stroke(); }
    ctx.fillStyle = ACCENT;
    ctx.beginPath(); ctx.arc(X(t), Y(0), 4, 0, 2 * Math.PI); ctx.fill();
    ctx.fillStyle = MUTED; ctx.font = "11px sans-serif";
    ctx.fillText("retract O: fibre dim " + (t > 0 ? "1" : "0"), x0 + 2, y1 + 10);
    ctx.fillText("t", x1 - 6, y0 + 16);

    // ---- right panel: the bump and the test function ----
    var a0 = half + 10, a1 = W - 10, sMin = -16, sMax = 1.5;
    function S(s) { return a0 + (s - sMin) / (sMax - sMin) * (a1 - a0); }
    function V(v) { return y0 - v / 1.1 * (y0 - y1); }
    ctx.strokeStyle = MUTED; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(a0, y0); ctx.lineTo(a1, y0); ctx.stroke();
    function curve(fn, color, dash) {
      ctx.strokeStyle = color; ctx.lineWidth = 1.5; ctx.setLineDash(dash);
      ctx.beginPath();
      for (var i = 0; i <= 600; i++) {
        var s = sMin + (sMax - sMin) * i / 600, v = fn(s);
        if (i === 0) ctx.moveTo(S(s), V(v)); else ctx.lineTo(S(s), V(v));
      }
      ctx.stroke(); ctx.setLineDash([]);
    }
    curve(f, FG, [4, 3]);
    var pos = t > 0 ? -Math.exp(1 / t) : -Infinity;
    if (t > 0) curve(function (s) { return beta(s - pos) ; }, ACCENT, []);
    ctx.fillStyle = MUTED;
    ctx.fillText(t > 0 ? "beta_t (solid), f (dashed)" : "t <= 0: pi_t = 0, no bump", a0 + 2, y1 + 10);
    ctx.fillText("s", a1 - 6, y0 + 16);

    // ---- numbers ----
    var line;
    if (t > 0) {
      var ip = 0, M = 3000, lo = pos - 1, hi = pos + 1, dh = (hi - lo) / M;
      for (var j = 0; j < M; j++) { var s = lo + j * dh; ip += f(s) * beta(s - pos); }
      ip *= dh;
      var e = Math.exp(1 / t);
      var bound = Math.exp(-0.1 * e) / t;
      line = "bump centred at s = -e^{1/t} = " + (pos > -1e6 ? pos.toFixed(2) : pos.toExponential(2)) +
        ";  coefficient <f, beta_t> = " + ip.toExponential(3) +
        "<br>difference-quotient bound one level up, e^{-0.1 e^{1/t}}/t = " +
        (bound > 1e-300 ? bound.toExponential(3) : "0") + ";  on a single level, 1/t = " + (1 / t).toFixed(2);
    } else {
      line = "t <= 0: the retraction is (t, f) -> (t, 0); the fibre of O is a point." +
        "<br>Move t to the right: the fibre becomes a line, and the bump that spans it comes in from -infinity.";
    }
    info.innerHTML = line;
  }
  inp.addEventListener("input", draw);
  window.addEventListener("resize", draw);
  draw();
})();
