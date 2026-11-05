#!/usr/bin/env python3
"""Check that every Lean declaration cited in a Markdown report exists.

Collects every backticked identifier of the form `Polyfold.…` (several may share one pair of
backticks, separated by commas or spaces), writes a Lean file that `#check`s each of them, runs it
in the project environment (`lake env lean`, with `~/.elan/bin` on the PATH), and reports the names
Lean cannot resolve.

Usage: python3 check_names.py Verification.md [more.md ...]
Exit status 0 if every name resolves.

Only declarations of the built library can be checked: a name declared in `Polyfold/Test.lean`
(which `import Polyfold` does not reach) is reported as unresolved here even though
`check_trace.py` resolves it in the source; cite such names without the `Polyfold.` prefix.
"""
import os, re, subprocess, sys, tempfile

# ---- project configuration -------------------------------------------------------------------
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)            # the Lake project folder (where lakefile.toml is)
MODULES = ["Polyfold"]                  # root modules to import; also the cited name prefixes
LEAN_OPTS = ["-DmaxSynthPendingDepth=3"]
# ------------------------------------------------------------------------------------------------

NAME = re.compile(r"\b((?:" + "|".join(MODULES) + r")(?:\.[^\W\d][\w'!?₀-₉ₐ-ₜ]*)+)")  # \w is Unicode-aware


def names_in(path):
    text = open(path, encoding="utf-8").read()
    found = []
    for code in re.findall(r"`([^`\n]+)`", text):
        if re.match(r"\s*(import|lake|open)\b", code):
            continue  # module paths in commands, not declarations
        found += NAME.findall(code)
    return found


def run_lean(src):
    """Elaborate `src` in the project environment; return Lean's output."""
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=HERE) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(["lake", "env", "lean"] + LEAN_OPTS + [tmp],
                           cwd=ROOT, capture_output=True, text=True, env=env)
    finally:
        os.unlink(tmp)
    return r.stdout + r.stderr


def main(paths):
    names = sorted({n.rstrip(".") for p in paths for n in names_in(p)})
    if not names:
        print("no Lean names cited")
        return 0
    checks = "\n".join(f"#check @{n}" for n in names) + "\n"
    out = run_lean("".join(f"import {m}\n" for m in MODULES) + "\n" + checks)
    if re.search(r"object file .* does not exist|unknown module prefix", out):
        print("could not check: the project is not built (or is being rebuilt) — run `lake build` first")
        for l in out.splitlines()[:3]:
            print("  lean:", l)
        return 2
    bad = sorted(set(re.findall(r"[Uu]nknown (?:identifier|constant) [`'‘]([^`'’]+)[`'’]", out)))
    print(f"{len(names)} distinct names cited, {len(names) - len(bad)} resolved, {len(bad)} unresolved")
    for b in bad:
        print("  unresolved:", b)
    other = [l for l in out.splitlines() if "error" in l and "nknown identifier" not in l
             and "nknown constant" not in l]
    for l in other[:10]:
        print("  lean:", l)
    return 1 if bad or other else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:] or [os.path.join(HERE, "Verification.md")]))
