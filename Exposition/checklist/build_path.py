#!/usr/bin/env python3
"""One-theorem path: what a reader checks to trust Theorem 16.6.6, leaves first.

usage (from the project folder, after `lake env lean Exposition/checklist/TrustedBase.lean`):
    python3 Exposition/checklist/build_path.py

Lean checks every proof, so a reader checks only the statements of the theorem and the
definitions those statements use, transitively.  This script takes the statement cone of the
roots below in graph.tsv, assigns each constant to a comparison row as build_checklist.py does
(rows of the constant's own or an earlier chapter, greedy cover), and orders the rows by level:
level 0 uses no other row of the cone, level k uses rows of level < k only.
"""
import json, re, collections, os, sys
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
OUT = os.path.join(EXP, 'Path-16.6.6.md')
CMP = os.path.join(EXP, 'cmp', 'ch%02d.json')
TEX = os.path.join(EXP, 'worked-example', 'WorkedExample-Mathematics.tex')
ROOTS = ['Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional',
         'Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional']

rows = {}; rowidx = {}; decl2rows = collections.defaultdict(list)
for n in range(1, 20):
    if not os.path.exists(CMP % n): continue
    for x in json.load(open(CMP % n))['items']:
        rowidx[x['id']] = len(rows); rows[x['id']] = x
        for d in x['lean'].get('decls', []):
            decl2rows['Polyfold.' + d.split(' · ')[1].strip()].append(x['id'])
graph = {}; mod = {}
for line in open(os.path.join(HERE, 'graph.tsv')):
    if line.strip():
        p, k, m, ds = line.rstrip('\n').split('\t'); graph[p] = ds.split() if ds else []; mod[p] = m
mains = {}
for line in open(os.path.join(HERE, 'mains.tsv')):
    if line.strip():
        lab, nm, k, m, ds = line.rstrip('\n').split('\t'); mains[nm] = (lab.split('|', 1)[1], m, ds.split() if ds else [])
for r in ROOTS:
    assert r in mains, r

short = lambda n: n[len('Polyfold.'):] if n.startswith('Polyfold.') else n
fileof = lambda m: m.replace('Polyfold.', '', 1).replace('.', '/') + '.lean'
chap = lambda rid: int(rid[1:].split('.')[0])
modchap = lambda x: int(re.match(r'Polyfold\.Chapter(\d+)', mod[x]).group(1))

cone = set(); st = [d for r in ROOTS for d in mains[r][2]]
while st:
    x = st.pop()
    if x in cone: continue
    cone.add(x); st += graph.get(x, [])
cone &= set(graph)

# statement rows of the roots
rootrows = collections.OrderedDict()
for r in ROOTS:
    rs = [q for q in decl2rows.get(r, []) if 'Theorem 16.6.6' in rows[q]['book']['label']] or decl2rows.get(r, [])
    for q in rs: rootrows.setdefault(q, []).append(r)

mapped = {x for x in cone if x in decl2rows}
cand = {x: ([q for q in decl2rows[x] if chap(q) <= modchap(x)] or decl2rows[x]) for x in mapped}
assign = {}; left = set(mapped)
while left:
    cnt = collections.Counter(q for x in left for q in cand[x])
    best = max(cnt, key=lambda q: (cnt[q], 'Definition' in rows[q]['book']['label'], -rowidx[q]))
    for x in [x for x in left if best in cand[x]]: assign[x] = best; left.discard(x)
row_nodes = collections.defaultdict(set)
for x, q in assign.items(): row_nodes[q].add(x)
rg = collections.defaultdict(set)
for x, q in assign.items():
    for d in graph.get(x, []):
        if d in assign and assign[d] != q: rg[q].add(assign[d])

# strongly connected components, then levels on the condensation
index = {}; low = {}; stack = []; on = set(); comps = []; c = [0]
def tarjan(v):
    index[v] = low[v] = c[0]; c[0] += 1; stack.append(v); on.add(v)
    for w in sorted(rg[v], key=lambda q: rowidx[q]):
        if w not in index: tarjan(w); low[v] = min(low[v], low[w])
        elif w in on: low[v] = min(low[v], index[w])
    if low[v] == index[v]:
        comp = []
        while True:
            w = stack.pop(); on.discard(w); comp.append(w)
            if w == v: break
        comps.append(comp)
for v in sorted(row_nodes, key=lambda q: rowidx[q]):
    if v not in index: tarjan(v)
compof = {q: i for i, comp in enumerate(comps) for q in comp}
level = {}
for i, comp in enumerate(comps):           # Tarjan emits components in reverse topological order
    deps = {compof[w] for q in comp for w in rg[q]} - {i}
    lv = 1 + max((level[j] for j in deps), default=-1)
    level[i] = lv
rowlevel = {q: level[compof[q]] for q in row_nodes}
unmapped = sorted((x for x in cone if x not in decl2rows), key=lambda x: (mod[x], x))

# where the worked example checks a definition: section titles of the plain note citing its number
tex = open(TEX).read()
secs = [(m.start(), m.group(2)) for m in re.finditer(r'\\(sub)?section\*?\{((?:[^{}]|\{[^{}]*\})*)\}', tex)]
def section_at(pos):
    t = None
    for s, title in secs:
        if s <= pos: t = title
    return t
def clean(t): return re.sub(r'\$([^$]*)\$', r'\1', re.sub(r'\\texorpdfstring\{([^{}]*)\}\{([^{}]*)\}', r'\1', t)).replace('\\C', 'ℂ').replace('\\ell', 'ℓ').replace('\\lambda', 'λ')
def example_refs(q):
    nums = re.findall(r'(?:Definition|Definitions|Theorem|Proposition|Lemma|Remark) ((?:\d+\.){2}\d+)', rows[q]['book']['label'])
    found = []
    for n in nums:
        for m in re.finditer(r'(?:Definition|Definitions|Theorem|Proposition|Lemma|Remark)s?[^.]{0,40}?\b' + re.escape(n) + r'\b', tex):
            s = section_at(m.start())
            if s and clean(s) not in found: found.append(clean(s))
    return found

def esc(s): return s.replace('|', '\\|')
def page(q):
    m = re.search(r'(?<!preprint )(?<!2017 )\bpp?\. [\d–-]+', rows[q]['book']['label'])
    return m.group(0) if m else ''
def title(q):
    t = rows[q]['title']
    return re.sub(r' \((?:2017|preprint)[^)]*\)', '', t)
VERD = {'same': 'as in the book', 'restated': 'restated', 'stronger': 'stronger', 'explicit': 'hypotheses explicit',
        'extra': 'extra', 'narrower': 'narrower', 'nothing': 'nothing to formalize'}
out = []; w = out.append
defrows = [q for q in row_nodes if q not in rootrows]
nlev = max(rowlevel[q] for q in defrows) + 1
w('# Checking one theorem: Theorem 16.6.6\n\n')
w('*Generated by `Exposition/checklist/build_path.py` from the Lean environment and the comparison pages; do not edit by hand.*\n\n')
w('Lean checks every proof. To trust Theorem 16.6.6 (p. 739), a reader therefore checks two things and nothing '
  'else: that the formal statement says what the book says, and that every definition the statement uses, '
  'directly or through other definitions, is the book\'s notion. The lemmas and the proof in between are checked '
  'by Lean.\n\n')
w(f'This page lists exactly those items for the two formal versions of the theorem (index `m + 1` and index 0): '
  f'{len(rootrows)} statement row{"s" if len(rootrows) != 1 else ""}, then {len(defrows)} definition rows in '
  f'{nlev} levels, leaves first. A row of level 0 uses no other row on this page; a row of level k uses only rows '
  f'of lower levels, so a reader who goes top to bottom always knows the notions a row is built from. '
  f'Each row id (V3.14, …) is an entry of the comparison page (`Exposition/Comparison.md`, or '
  f'`polyfold-beside-lean.html` in a browser), which gives the book text, the Lean declarations and the '
  f'verdict. The column *Examples* names the section of the worked example '
  f'(`Exposition/WorkedExample-Mathematics.pdf`) where the definition is used on the orbifold ℂ/ℤ₅, and the '
  f'Lean examples and non-examples of the definition, where there are any.\n\n')
w('A whole-book version of this list, in tiers, is `Exposition/ReviewerChecklist.md`.\n\n')
w('## 1. The statement\n\n| Row | Book | Lean declaration |\n|---|---|---|\n')
for q, rs in rootrows.items():
    w(f"| {q} | {esc(rows[q]['book']['label'])} | " + ', '.join(f'`{short(r)}` ({fileof(mains[r][1])})' for r in rs) + ' |\n')
w('\nRead the statement first: it names the notions the definitions below make precise. '
  'One hypothesis is written out that the quoted statement leaves to the definitions: “$f$ oriented '
  'sc-Fredholm” is read with tame germ data of the model section at every smooth point, as Definition 3.6.3 '
  '(p. 135) asks of the germs of a tame strong bundle, together with the Fredholm index; both are the fields '
  'of `CanonicalGermInput` (row V3.103 below; Findings, Chapter 3, item 191).\n\n')
RISKY = ('explicit', 'stronger', 'narrower', 'extra')
risky = sorted((q for q in defrows if rows[q]['verdict'] in RISKY), key=lambda q: (rowlevel[q], rowidx[q]))
EXF = os.path.join(HERE, 'path_examples.tsv')
examples = collections.defaultdict(list)          # row -> [(Lean declaration, kind, what it shows)]
if os.path.exists(EXF):
    for line in open(EXF):
        if line.strip() and not line.startswith('#'):
            q, d, k, t = line.rstrip('\n').split('\t')[:4]
            t = re.sub(r'^(existing|reused)\s*:\s*', '', t.strip(), flags=re.I).rstrip('. ')
            examples[q].append((d, k, t[:1].upper() + t[1:]))
lc = lambda t: t[:1].lower() + t[1:] if len(t) > 1 and t[1].islower() else t
KINDS = (('example', 'Example'), ('non-example', 'Non-example'), ('property', 'Property'))
def excell(q):
    parts = []
    ex = example_refs(q)
    if ex: parts.append('In the worked example: ' + '; '.join(ex) + '.')
    for k, lab in KINDS:
        xs = [t for d, kk, t in examples[q] if kk == k]
        if xs: parts.append(f'{lab}: {lc(xs[0])}' + (f' (+{len(xs) - 1})' if len(xs) > 1 else '') + '.')
    return esc(' '.join(parts))
w(f'## 2. Read first: where the formal definition differs from the text ({len(risky)} rows)\n\n'
  'Most rows below say what the book says, in the book\'s order (verdict *as in the book*) or in an equivalent '
  'form (*restated*). The rows of this section differ more: a hypothesis the text leaves implicit is written '
  'out (*hypotheses explicit*), the formal notion is stronger or narrower than the text\'s, or the row is a '
  'construction the text uses without a numbered statement (*extra*). A mismatch is most likely here, so these '
  'rows come first; the column *What differs* is the short summary of the comparison page.\n\n'
  '| Row | Book | Level | Verdict | What differs | Examples |\n|---|---|---|---|---|---|\n')
for q in risky:
    w(f"| {q} | {esc(title(q))} | {rowlevel[q]} | {VERD[rows[q]['verdict']]} | "
      f"{esc('; '.join(rows[q].get('chips', [])))} | {excell(q)} |\n")
w('\n## 3. All definitions, leaves first\n\n'
  'Rows of section 2 are marked ◆.\n\n')
for lv in range(nlev):
    rs = sorted((q for q in defrows if rowlevel[q] == lv), key=lambda q: rowidx[q])
    if not rs: continue
    w(f'### Level {lv} ({len(rs)} row{"s" if len(rs) != 1 else ""})\n\n| Row | Book | Page | Verdict | Examples |\n|---|---|---|---|---|\n')
    for q in rs:
        mark = ' ◆' if q in risky else ''
        w(f"| {q}{mark} | {esc(title(q))} | {page(q)} | {VERD.get(rows[q]['verdict'], rows[q]['verdict'])} | "
          f"{excell(q)} |\n")
    w('\n')
if examples:
    w('## 4. The examples in Lean\n\n'
      'Every example, non-example and property cited above, with its Lean declaration (files in '
      '`Polyfold/Examples/Path/` or earlier in the library). Lean has checked each one, with only the standard '
      'axioms. Sections 2 and 3 show the first of each kind; the number in parentheses counts the others.\n\n')
    for q in risky + [q for q in defrows if q not in risky and examples[q]]:
        if not examples[q]: continue
        w(f"**{q}**, {esc(title(q))}\n\n")
        for k, lab in KINDS:
            for d, kk, t in examples[q]:
                if kk == k: w(f'* {lab}: {t} (`{short(d)}`)\n')
        w('\n')
if unmapped:
    w(f'## 5. Helper definitions without a row of their own ({len(unmapped)})\n\n'
      'Accessors, coercions, instances and auxiliary constructions that the statement reaches but that have no '
      'numbered counterpart in the book. Each is short; they are listed by file.\n\n<details><summary>The list</summary>\n\n')
    byf = collections.defaultdict(list)
    for x in unmapped: byf[fileof(mod[x])].append(short(x))
    for f, xs in sorted(byf.items()):
        w(f"* {f}: " + ', '.join(f'`{x}`' for x in xs) + '\n')
    w('\n</details>\n')
open(OUT, 'w').write(''.join(out))
print('cone constants', len(cone), 'statement rows', len(rootrows), 'definition rows', len(defrows),
      'levels', nlev, 'helpers', len(unmapped),
      'rows with example section', sum(1 for q in defrows if example_refs(q)), 'risky', len(risky),
      'risky with Lean examples', sum(1 for q in risky if examples[q]))
