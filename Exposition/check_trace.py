"""Trace-tag checker for "Polyfold Theory, proof by proof" (Exposition/ProofByProof.md).

Adapted from the Morse project. A tag's path is relative to the Lean library root `Polyfold/`
(this project: `Polyfold/Polyfold/<path>.lean`), or begins with `Mathlib/`.

Usage: python3 Exposition/check_trace.py Exposition/ProofByProof.md

A tag has the form  ⟦Chapter1/ChainRule · theorem_1_21⟧ .
For each tag we find the declaration in <LIB>/<path>.lean, record its line number and full
name, and extract the declaration header (the statement, up to ':=' or 'where').
"""
import re, sys, json, pathlib, collections

# ---- project configuration -------------------------------------------------------------------
_PROJ = pathlib.Path(__file__).resolve().parents[1]   # the project folder (Polyfold/)
LIB = 'Polyfold'                                       # the Lean library root inside it
ROOT = _PROJ / LIB
MATHLIB = _PROJ / '.lake' / 'packages' / 'mathlib'
DEPS = {}   # other Lake dependencies: {'Prefix/': path to their library root}
# ------------------------------------------------------------------------------------------------

TAG = re.compile(r'⟦([A-Za-z0-9_/]+) · ([^⟧]+?)⟧')
KW = r'(?:theorem|lemma|def|irreducible_def|abbrev|instance|structure|class|inductive|opaque)'
DECL = re.compile(r'^(\s*)(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|nonrec|partial|unsafe|meta)\s+)*'
                  + KW + r'\s+([^\s:({\[⦃]+)')

_cache = {}

def source_file(path):
    """The Lean file a tag path names."""
    if path.startswith('Mathlib/'):
        return MATHLIB / (path + '.lean')
    for prefix, root in DEPS.items():
        if path.startswith(prefix):
            return root / (path[len(prefix):] + '.lean')
    return ROOT / (path + '.lean')

def decls(path):
    """Return list of (line_no, declared_token, namespace_prefix) for a file."""
    if path in _cache:
        return _cache[path]
    f = source_file(path)
    if not f.exists():
        _cache[path] = None
        return None
    lines = f.read_text().split('\n')
    out = []
    ns = []
    for i, l in enumerate(lines, 1):
        m = re.match(r'^\s*namespace\s+([\w.]+)', l)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r'^\s*end\s+([\w.]+)\s*$', l)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = DECL.match(l)
        if m:
            out.append((i, m.group(2), '.'.join(ns)))
    _cache[path] = (lines, out)
    return _cache[path]

def resolve(path, name):
    d = decls(path)
    if d is None:
        return None
    lines, out = d
    name = name.strip()
    cands = []
    for (i, tok, ns) in out:
        root = tok.startswith('_root_.')
        t = tok[len('_root_.'):] if root else tok
        full = t if root else (ns + '.' + t if ns else t)
        if full == name or full.endswith('.' + name):
            cands.append((i, full))
    if not cands:
        return None
    i, full = cands[0]
    # extract the header: from the declaration line to ':=' / 'where'
    hdr = []
    for j in range(i - 1, min(i - 1 + 40, len(lines))):
        l = lines[j]
        hdr.append(l)
        s = re.sub(r'--.*$', '', l)
        if re.search(r':=\s*(by\b.*)?$', s) or re.search(r':=\s', s) or re.search(r'\bwhere\s*$', s):
            break
    text = '\n'.join(hdr)
    text = re.sub(r'\s*:=\s*by\b.*$', ' := …', text, flags=re.S)
    text = re.sub(r'\s*:=\s*$', ' := …', text)
    return {'line': i, 'full': full, 'header': text.rstrip()}

def check(md_paths):
    report = collections.OrderedDict()
    bad = []
    for p in md_paths:
        txt = pathlib.Path(p).read_text()
        for m in TAG.finditer(txt):
            path, name = m.group(1), m.group(2)
            key = (path, name)
            r = resolve(path, name)
            if r is None:
                bad.append((p, path, name))
            else:
                report.setdefault(key, {**r, 'where': []})['where'].append(pathlib.Path(p).name)
    return report, bad

if __name__ == '__main__':
    rep, bad = check(sys.argv[1:])
    print(f'{len(rep)} distinct declarations cited, {len(bad)} unresolved tags')
    for b in bad:
        print('UNRESOLVED', *b)
    sys.exit(1 if bad else 0)
