// Interactive figure for Chapter 3: a contraction germ, its solution germ, and the shrinking of the
// germ in the germ implicit function theorem (Theorem 3.33).  Plain JavaScript, no libraries.  Finds
// the div with id "germ-figure" and draws a canvas with three sliders: the parameter a, the level m
// and the order k.
//
// The model (see fig3-germ.py): W = sequences with |w|_m^2 = sum_k e^{2mk} |w_k|^2, parameter
// a in [0, infinity), B(a, w) = a w + beta(a), beta(a)_k = a e^{-k/a}.  The solution germ is
// delta(a) = beta(a)/(1 - a), with |delta(a)|_m^2 = (a/(1-a))^2 q/(1-q), q = e^{2(m - 1/a)}, finite iff
// a < 1/m.  The germ of the contraction germ is N(m) = (-1/(m+2), 1/(m+2)); the proof of Theorem 3.33
// certifies delta to be sc^k on N(m + s_k) with s_k = 2^k - 1, i.e. on [0, 1/(m + 2^k + 1)).
//
// Top: log10 |delta(a)|_j against a for the levels j = 0..5 (the selected level m bold), the current
// parameter a marked, and below the axis three bands: where delta(a) lies in W_m (grey), the germ N(m)
// (dark) and the shrunken germ N(m + s_k) (accent).  Below: the numbers.
(function () {
  var root = document.getElementById("germ-figure");
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

  function slider(label, min, max, step, value) {
    var row = document.createElement("div");
    row.style.margin = "4px 0";
    var lab = document.createElement("label");
    lab.textContent = label + " ";
    lab.style.display = "inline-block";
    lab.style.minWidth = "5.5em";
    var inp = document.createElement("input");
    inp.type = "range"; inp.min = min; inp.max = max; inp.step = step; inp.value = value;
    inp.style.width = "55%"; inp.style.verticalAlign = "middle";
    var out = document.createElement("span");
    out.style.marginLeft = "6px";
    row.appendChild(lab); row.appendChild(inp); row.appendChild(out);
    root.appendChild(row);
    inp.addEventListener("input", draw);
    return { inp: inp, out: out };
  }
  var sa = slider("parameter a", 0.01, 0.7, 0.005, 0.3);
  var sm = slider("level m", 0, 5, 1, 2);
  var sk = slider("order k", 0, 3, 1, 1);
  var info = document.createElement("div");
  info.style.marginTop = "6px"; info.style.lineHeight = "1.5";
  root.appendChild(info);

  // |delta(a)|_m, or Infinity when delta(a) is not in W_m
  function normDelta(a, m) {
    if (a <= 0 || a >= 1) return a <= 0 ? 0 : Infinity;
    if (m > 0 && a * m >= 1) return Infinity;
    var q = Math.exp(2 * (m - 1 / a));
    return a / (1 - a) * Math.sqrt(q / (1 - q));
  }
  function sk_(k) { return Math.pow(2, k) - 1; }
  function radius(m, k) { return 1 / (m + sk_(k) + 2); }

  var AMAX = 0.72, YMIN = -12, YMAX = 2;

  function draw() {
    var a = parseFloat(sa.inp.value), m = parseInt(sm.inp.value, 10), k = parseInt(sk.inp.value, 10);
    sa.out.textContent = a.toFixed(3);
    sm.out.textContent = String(m);
    sk.out.textContent = k + "  (s_k = " + sk_(k) + ")";
    var W = root.clientWidth || 360, H = Math.round(Math.max(240, W * 0.55));
    var dpr = window.devicePixelRatio || 1;
    canvas.width = W * dpr; canvas.height = H * dpr; canvas.style.height = H + "px";
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = BG; ctx.fillRect(0, 0, W, H);

    var x0 = 38, x1 = W - 10, y1 = 10, y0 = H - 70;
    function X(t) { return x0 + t / AMAX * (x1 - x0); }
    function Y(v) { return y0 - (v - YMIN) / (YMAX - YMIN) * (y0 - y1); }

    // axes
    ctx.strokeStyle = MUTED; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(x0, y1); ctx.lineTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();
    ctx.fillStyle = MUTED; ctx.font = "11px sans-serif";
    for (var v = YMIN; v <= YMAX; v += 4) {
      ctx.fillText(String(v), 4, Y(v) + 4);
      ctx.beginPath(); ctx.moveTo(x0 - 3, Y(v)); ctx.lineTo(x0, Y(v)); ctx.stroke();
    }
    for (var t = 0; t <= 0.7001; t += 0.1) {
      ctx.fillText(t.toFixed(1), X(t) - 8, y0 + 13);
    }
    ctx.fillText("log10 |delta(a)|_j", x0 + 6, y1 + 10);

    // the curves
    for (var j = 0; j <= 5; j++) {
      ctx.strokeStyle = j === m ? ACCENT : MUTED;
      ctx.lineWidth = j === m ? 2.2 : 0.8;
      ctx.beginPath();
      var started = false;
      for (var i = 1; i <= 600; i++) {
        var aa = i / 600 * AMAX, nd = normDelta(aa, j);
        if (!isFinite(nd) || nd <= 0) { started = false; continue; }
        var yy = Math.log(nd) / Math.LN10;
        if (yy < YMIN) { started = false; continue; }
        yy = Math.min(yy, YMAX);
        if (!started) { ctx.moveTo(X(aa), Y(yy)); started = true; } else ctx.lineTo(X(aa), Y(yy));
      }
      ctx.stroke();
      if (j >= 2 && 1 / j < AMAX) {
        ctx.setLineDash([2, 3]); ctx.strokeStyle = j === m ? ACCENT : MUTED; ctx.lineWidth = 0.6;
        ctx.beginPath(); ctx.moveTo(X(1 / j), y1); ctx.lineTo(X(1 / j), y0); ctx.stroke();
        ctx.setLineDash([]);
      }
    }

    // the current point
    var nda = normDelta(a, m);
    ctx.strokeStyle = FG; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(X(a), y1); ctx.lineTo(X(a), y0); ctx.stroke();
    if (isFinite(nda) && nda > 0) {
      var ya = Math.log(nda) / Math.LN10;
      if (ya >= YMIN && ya <= YMAX) {
        ctx.fillStyle = ACCENT; ctx.beginPath(); ctx.arc(X(a), Y(ya), 4, 0, 2 * Math.PI); ctx.fill();
      }
    }

    // the three bands below the axis
    var dom = m === 0 ? AMAX : Math.min(1 / m, AMAX);
    var bands = [
      [dom, MUTED, 0.45, "delta(a) in W_" + m],
      [radius(m, 0), FG, 0.75, "N(" + m + ")"],
      [radius(m, k), ACCENT, 0.9, "N(" + m + " + " + sk_(k) + ")"]
    ];
    for (var b = 0; b < 3; b++) {
      var yb = y0 + 20 + b * 15;
      ctx.globalAlpha = bands[b][2]; ctx.fillStyle = bands[b][1];
      ctx.fillRect(X(0), yb, X(bands[b][0]) - X(0), 10);
      ctx.globalAlpha = 1; ctx.fillStyle = FG; ctx.font = "11px sans-serif";
      var tx = X(bands[b][0]) + 4;
      if (tx > x1 - 90) tx = x1 - 90;
      ctx.fillText(bands[b][3], tx, yb + 9);
    }

    var inW = m === 0 || a < 1 / m;
    var cert = a < radius(m, k);
    info.innerHTML =
      "delta(a) lies in W_" + m + " exactly for a &lt; " + (m === 0 ? "1 (every a of the germ)" : "1/" + m +
        " = " + (1 / m).toFixed(3)) + "; at a = " + a.toFixed(3) + ": " +
      (inW ? "|delta(a)|_" + m + " = " + nda.toExponential(3) : "not on level " + m) + ".<br>" +
      "Germ of the contraction germ on level " + m + ": N(" + m + ") = [0, 1/" + (m + 2) + ") = [0, " +
        radius(m, 0).toFixed(3) + ").<br>" +
      "The proof certifies sc<sup>" + k + "</sup> on N(" + m + " + " + sk_(k) + ") = [0, 1/" +
        (m + sk_(k) + 2) + ") = [0, " + radius(m, k).toFixed(3) + "); a = " + a.toFixed(3) +
        (cert ? " is inside." : " is outside.") +
      "<br>In this example delta is in fact sc-smooth on N(m) itself: the shrinking is the price of the proof.";
  }

  window.addEventListener("resize", draw);
  draw();
})();
