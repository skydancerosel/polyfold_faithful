"""Build the comparison edition: the book's statements beside the formal ones.

Usage: python3 Exposition/build_comparison.py [outdir]

Assembles Exposition/Comparison.json from the per-part files Exposition/cmp/*.json (in file-name
order; a new part is picked up by its file name alone), checks every declaration tag against the Lean
sources, and writes Comparison.md and the web page polyfold-beside-lean.html (default: into
Exposition/). Source paths are printed relative to the project folder (`Polyfold/Chapter1/….lean`).

Data format (one row per result; see cmp/ch01.json):
  {"id": "V1.5", "title": …, "verdict": one of VERDICTS,
   "book": {"label": "§1.1, Proposition 1.6, p. 7", "page": 7, "statement": …, "note": …},
   "lean": {"statement": …, "decls": ["Chapter1/ScBanach · ScBanach.proposition_1_1_7", …]},
   "chips": [short strings], "diff": [bullets]}
and "notFormalized": [{"title", "label", "page", "book", "instead"}]; an entry proved later gets
"formalized": [the ids of the rows that prove it] and "decls": [...], keeps its place (so the G-numbers of
the later entries do not move) and is shown with the verdict "formalized since". An entry may fix its
number with "g": k (an integer); it then keeps G.k wherever it stands, and the entries without "g" are
numbered by position among themselves, so an entry with "g" can be added to an earlier part without
moving the G-numbers of later parts. The Morse project's key
`milnor` for the book column is still accepted and renamed on load.
"""
import re, sys, json, html, pathlib, collections

EXDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(EXDIR))
import check_trace as T

# ---- project configuration -------------------------------------------------------------------
PROJECT = 'Polyfold'                       # the Lean library root and module prefix
BOOK_SHORT = 'HWZ'                         # the author label of the left column
BOOK_KEY = 'book'                          # the JSON key of the left column
LEGACY_KEYS = ('milnor',)                  # older names of that key, accepted on load
TITLE = 'Polyfold Theory beside Lean'
H1 = 'Polyfold Theory <em>beside</em> Lean'
EYEBROW = 'Hofer–Wysocki–Zehnder · Polyfold and Fredholm Theory, Part I and Part II, Chapters 7–11 · the statements compared'
DEK = ('Every result of the book beside the statement the machine actually checked. The left column is '
       'Hofer, Wysocki and Zehnder, in their own terms, with the numbering and pages of the Springer edition '
       '(2021), followed in parentheses by those of the 2014 preprint (arXiv 1407.3185) for Part I and of the '
       'book’s arXiv version (1707.08941, “2017”) for Part II, from Chapter 7 on, which has no preprint; the '
       'correspondence is in Exposition/BookConcordance.md. The right column is the '
       'formal statement, with the hypotheses the text leaves to the reader written out. Click a declaration '
       'to see the Lean it names.')
OUT_HTML = 'polyfold-beside-lean.html'
OUT_PREVIEW = 'preview-cmp.html'
OUT_MD = 'Comparison.md'
FOOT = ('Left column: H. Hofer, K. Wysocki, E. Zehnder, <em>Polyfold and Fredholm Theory</em>, Part I '
        '(Springer 2021), paraphrased, with its numbers and pages, followed in parentheses by those of the 2014 '
        'preprint arXiv 1407.3185 (Part I) or of the book’s arXiv version 1707.08941 (Part II, Chapters 7–11, '
        'which has no preprint); see Exposition/BookConcordance.md. Right column: the statements proved in Lean 4 '
        'against Mathlib in Polyfold/*.lean, checked by Lean’s kernel, depending only on propext, '
        'Classical.choice and Quot.sound. Every declaration named here was resolved mechanically in the '
        'source. Companion texts: Exposition/Verification.md, Exposition/ProofByProof.md.')
CHAPTERS = [
    ('V1', 'Chapter 1', 'HWZ Chapter 1 §§1.1–1.4, pp. 5–20 (preprint pp. 6–17): sc-Banach spaces, sc-operators, '
           'sc-Fredholm operators, sc-differentiability, the chain rule, the degeneracy index'),
    ('V2', 'Chapter 2', 'HWZ Chapter 2 §§2.1, 2.3–2.7, pp. 21–88 (preprint §§2.1–2.6, pp. 18–60): sc-smooth retractions and retracts, M-polyfolds, '
           'the degeneracy index, tame M-polyfolds and their faces, fibred products, strong bundles'),
    ('V3', 'Chapter 3', 'HWZ Chapter 3: sc-Fredholm sections and the implicit function theorem'),
    ('V4', 'Chapter 4', 'HWZ Chapter 4 §§4.1–4.4, pp. 175–204 (preprint pp. 147–168): manifolds with boundary with corners — '
           'sc⁺-retracts and the characterization, smooth finite-dimensional submanifolds, families and Sard’s theorem'),
    ('V5', 'Chapter 5', 'HWZ Chapter 5 §§5.1–5.3, 5.5, pp. 205–236 (preprint §§5.1–5.4, pp. 169–199): the Fredholm package for M-polyfolds — '
           'auxiliary norms, compactness, sc⁺-sections and bump functions, transversality, general and good position, '
           'homotopies, partitions of unity'),
    ('V6', 'Chapter 6', 'HWZ Chapter 6 §§6.2–6.8, pp. 237–286 (preprint §§6.1–6.7, pp. 200–237): linearizations, the determinant of Fredholm '
           'operators and its orientation, the determinant bundle, local propagation and orientations of sc-Fredholm '
           'sections, the orientation of the solution set, the product with [0, 1]; Theorem 6.7.1 (preprint 6.43) is not formalized'),
    ('V7', 'Part II, Chapter 7', 'HWZ Part II, Chapter 7 §§7.1–7.3, 7.5–7.6, pp. 287–356 (2017 §§7.1–7.5, pp. 225–256; '
           'Part II has no 2014 preprint): ep-groupoids, natural representations of the '
           'isotropy groups, local uniformizers, ep-subgroupoids, effective and reduced ep-groupoids, the topology of '
           'the orbit space, index lifting, paracompact orbit spaces, proper subsets, sc-smooth partitions of unity'),
    ('V8', 'Part II, Chapter 8', 'HWZ Part II, Chapter 8 §§8.1–8.3, 8.5–8.6, pp. 357–400 (2017 §§8.1–8.5, pp. 257–289; '
           'Part II has no 2014 preprint): the tangent of an ep-groupoid and the tangent '
           'functor, sc-differential forms (not formalized), strong bundles over ep-groupoids and their sections, '
           'proper covering functors, covering functors of finite groupoids and geometric lifts, proper strong bundle '
           'coverings'),
    ('V9', 'Part II, Chapter 9', 'HWZ Part II, Chapter 9 §§9.1–9.5, pp. 401–453 (2017 Chapter 9, pp. 291–332; '
           'Part II has no 2014 preprint): branched ep⁺-subgroupoids and local branching structures, the tangent and '
           'the boundary, good points, orientations, the geometry of local branching structures, sets of measure '
           'zero and the canonical σ-algebras; branched integration and Stokes’ theorems are not formalized'),
    ('V10', 'Part II, Chapter 10', 'HWZ Part II, Chapter 10 §§10.1–10.6, pp. 461–520 (2017 Chapter 10, pp. 333–374; '
            'Part II has no 2014 preprint): equivalences of ep-groupoids and natural equivalences, the weak fibred '
            'product, localization at the system of equivalences and generalized maps, strong bundle equivalences, '
            'localization in the strong bundle case'),
    ('V11', 'Part II, Chapter 11', 'HWZ Part II, Chapter 11 §§11.1–11.6, pp. 521–566 (2017 Chapter 11, pp. 375–416; '
            'Part II has no 2014 preprint): the tangent functor and faces up to equivalence, branched '
            'ep⁺-subgroupoids under generalized isomorphisms, strong bundles up to equivalence, coverings and '
            'equivalences; sc-differential forms (§11.2) and integration (§11.4) are not formalized'),
    ('G', 'Not formalized', 'What the book states and the formalization does not prove, and what it does instead; '
          'an entry proved since the first edition of this page keeps its number and is marked “formalized since”'),
]
# ------------------------------------------------------------------------------------------------

def lean_file(path):
    """Where a tag's file really is, relative to the project folder."""
    if path.startswith('Mathlib/'):
        return path + '.lean'
    return PROJECT + '/' + path + '.lean'

VERDICTS = [
    ('same',      'as in the book',      'The formal statement is the book’s, hypothesis for hypothesis.'),
    ('explicit',  'hypotheses explicit', 'Same mathematics; the formal statement names what the book leaves implicit.'),
    ('stronger',  'stronger',            'The formal statement proves more than the book’s.'),
    ('narrower',  'narrower',            'The formal statement assumes more, or covers fewer cases.'),
    ('restated',  'restated',            'Same mathematics in a different formulation.'),
    ('extra',     'not in the book',     'A definition or a tool built for the formalization.'),
    ('sign',      'value differs',       'The formal value differs from the book’s, through a difference of convention.'),
    ('gap',       'not formalized',      'The book states it; the formalization does not prove it.'),
    ('closed',    'formalized since',    'Listed as not formalized in the first edition of this page; proved since, in the rows named.'),
]
VNAME = {k: n for k, n, _ in VERDICTS}

MATHS = re.compile(r'\$\$.+?\$\$|\$[^$]+?\$', re.S)


def chapter_of(vid):
    """Which chapter an item belongs to: V2.3 -> V2, G.2 -> G."""
    if vid.startswith('G.'):
        return 'G'
    m = re.match(r'(V\d+)\.', vid)
    return m.group(1) if m else '?'


def md(text):
    """Tiny markdown: math protected, then escaping, code spans and emphasis, then paragraphs."""
    if text is None:
        return ''
    keep = []

    def stash(m):
        keep.append(m.group(0).replace('&', '&amp;').replace('<', '&lt;'))
        return f'\x00{len(keep) - 1}\x00'

    s = MATHS.sub(stash, str(text))
    s = html.escape(s, quote=False)
    s = re.sub(r'`([^`]+)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'(?<![\w*])\*([^*\n]+)\*(?![\w*])', r'<em>\1</em>', s)
    s = re.sub(r'\x00(\d+)\x00', lambda m: keep[int(m.group(1))], s)
    paras = [p.strip() for p in re.split(r'\n\s*\n', s) if p.strip()]
    return ''.join('<p>' + p.replace('\n', ' ') + '</p>' for p in paras)


def plain(text):
    """Searchable plain text."""
    return re.sub(r'\s+', ' ', re.sub(r'[$*`\\]', ' ', str(text or ''))).strip()


def item_id(vid):
    # primes must survive slugification
    vid = vid.replace('′', '-prime').replace('″', '-prime2').replace("'", '-prime')
    return 'item-' + re.sub(r'[^A-Za-z0-9.-]+', '-', vid)


CHAPTER_ORDER = [p for p, _, _ in CHAPTERS]


def id_key(it):
    """Book order of an item id: chapter, then number, then primes (V1.10 < V1.10′ < V1.11)."""
    vid = it['id']
    m = re.match(r'(V\d+)\.(\d+)(.*)$', vid)
    if not m or m.group(1) not in CHAPTER_ORDER:
        return (len(CHAPTER_ORDER), 0, vid)
    return (CHAPTER_ORDER.index(m.group(1)), int(m.group(2)), m.group(3))


def normalize(it):
    """Accept the Morse project's key for the book column."""
    for k in LEGACY_KEYS:
        if k in it and BOOK_KEY not in it:
            it[BOOK_KEY] = it.pop(k)
    return it


def assemble():
    """Merge the per-part data files cmp/*.json, in file-name order, into Comparison.json.

    Items are sorted into book order by id; the notFormalized entries keep file order, so that the
    G-numbers of earlier parts do not move when a later part is appended. Without cmp/, the existing
    Comparison.json is used as it stands."""
    parts = sorted((EXDIR / 'cmp').glob('*.json'))
    if not parts:
        return
    items, gaps = [], []
    for f in parts:
        d = json.loads(f.read_text())
        items += [normalize(it) for it in d.get('items', [])]
        gaps += d.get('notFormalized', [])
    items.sort(key=id_key)
    (EXDIR / 'Comparison.json').write_text(
        json.dumps({'items': items, 'notFormalized': gaps}, ensure_ascii=False, indent=1) + '\n')
    print(f'Comparison.json assembled from {", ".join(f.name for f in parts)}')


def load():
    assemble()
    data = json.loads((EXDIR / 'Comparison.json').read_text())
    items = [normalize(it) for it in data['items']]
    if data.get('notFormalized'):
        pos = 0
        for g in data['notFormalized']:
            if isinstance(g.get('g'), int):
                k = g['g']                 # a fixed number (see the module docstring)
            else:
                pos += 1
                k = pos
            done = g.get('formalized') or []
            items.append({'id': f'G.{k}', 'title': g['title'], 'verdict': 'closed' if done else 'gap',
                          BOOK_KEY: {'label': g['label'], 'page': g.get('page'), 'statement': g['book']},
                          'lean': {'statement': g['instead'], 'decls': g.get('decls', [])},
                          'chips': [f'now {v}' for v in done], 'diff': []})
    return items


def validate(items):
    bad = []
    seen = set()
    for it in items:
        vid = it.get('id', '?')
        if vid in seen:
            bad.append(f'{vid}: duplicate id')
        seen.add(vid)
        if it.get('verdict') not in VNAME:
            bad.append(f'{vid}: verdict {it.get("verdict")!r}')
        for key in ('title', BOOK_KEY, 'lean'):
            if not it.get(key):
                bad.append(f'{vid}: missing {key}')
        if not it.get(BOOK_KEY, {}).get('statement'):
            bad.append(f'{vid}: empty {BOOK_SHORT} statement')
        if not it.get('lean', {}).get('statement'):
            bad.append(f'{vid}: empty formal statement')
        if not it.get('lean', {}).get('decls') and it.get('verdict') != 'gap':
            bad.append(f'{vid}: no declarations')
        for ch in it.get('chips', []):
            if len(ch) > 44:
                bad.append(f'{vid}: chip too long: {ch!r}')
    return bad


def resolve_decls(items):
    """Attach {path, name, line, header} to each declaration; return the list of failures."""
    bad = []
    for it in items:
        out = []
        for tag in it['lean']['decls']:
            m = re.match(r'^\s*([A-Za-z0-9_/]+)\s*·\s*(.+?)\s*$', tag)
            if not m:
                bad.append(f'{it["id"]}: malformed tag {tag!r}')
                continue
            path, name = m.group(1), m.group(2)
            r = T.resolve(path, name)
            if r is None:
                bad.append(f'{it["id"]}: unresolved {path} · {name}')
                continue
            out.append({'path': path, 'name': name, **r})
        it['_decls'] = out
    return bad


def render(items):
    head = (EXDIR / 'comparison-head.html').read_text()
    counts = collections.Counter(it['verdict'] for it in items)
    tally = ''.join(
        f'<span class="t"><span class="sw" style="background:var(--v-{k})"></span>'
        f'<b>{counts.get(k, 0)}</b> {html.escape(n)}</span>' for k, n, _ in VERDICTS)
    ndecl = len({(d['path'], d['name']) for it in items for d in it['_decls']})
    mast = f"""<header class="mast">
<p class="eyebrow">{EYEBROW}</p>
<h1>{H1}</h1>
<p class="dek">{DEK}</p>
<div class="tally"><span class="t"><b>{len(items)}</b> results</span>
<span class="t"><b>{ndecl}</b> declarations</span>{tally}</div>
<div class="howto"><b>How to read a row.</b> The left panel states the result as the book states it,
with the page. The right panel states what Lean proves, and every hypothesis in it is one the formal
proof really uses. Where the two differ, the strip underneath says how, and the label on the right of
the title says what kind of difference it is. The grey buttons are the declarations: click one to see
its exact statement in the source, with its file and line.</div>
</header>"""

    ctrl = ['<div class="controls" role="search">',
            '<input type="search" id="q" placeholder="Search statements, e.g. compact, quadrant, regularizing" '
            'aria-label="Search the statements">',
            '<div class="vset" role="group" aria-label="Filter by kind of difference">']
    for k, n, tip in VERDICTS:
        ctrl.append(f'<button class="vb" type="button" data-v="{k}" aria-pressed="true" title="{html.escape(tip)}">'
                    f'<span class="sw" style="background:var(--v-{k})"></span>{html.escape(n)}</button>')
    ctrl.append('</div><span class="shown" id="shown" aria-live="polite"></span></div>')

    nav = ['<nav class="chap" aria-label="Chapters">']
    body = []
    for prefix, name, sub in CHAPTERS:
        sel = [it for it in items if chapter_of(it['id']) == prefix]
        if not sel:
            continue
        cid = 'ch-' + prefix.replace('.', '')
        nav.append(f'<a href="#{cid}">{html.escape(name)}</a>')
        body.append(f'<section class="chapter" id="{cid}" data-n="{len(sel)}">'
                    f'<h2>{html.escape(name)}</h2><p class="csub">{html.escape(sub)}</p>')
        for it in sel:
            body.append(render_item(it))
        body.append('</section>')
    nav.append('</nav>')

    script = """<script>
(function(){
  var items=[].slice.call(document.querySelectorAll('article.item'));
  var chaps=[].slice.call(document.querySelectorAll('section.chapter'));
  var on={}; document.querySelectorAll('button.vb').forEach(function(b){on[b.dataset.v]=true;});
  var q=document.getElementById('q'), shown=document.getElementById('shown');
  function apply(){
    var t=(q.value||'').trim().toLowerCase(), n=0;
    items.forEach(function(el){
      var ok=on[el.dataset.v] && (!t || el.dataset.s.indexOf(t)>=0);
      el.hidden=!ok; if(ok) n++;
    });
    chaps.forEach(function(s){
      s.hidden=!s.querySelector('article.item:not([hidden])');
    });
    shown.textContent=n+' of '+items.length+' shown';
    var e=document.getElementById('none'); if(e) e.hidden=(n>0);
  }
  document.querySelectorAll('button.vb').forEach(function(b){
    b.addEventListener('click',function(){
      var v=b.dataset.v; on[v]=!on[v]; b.setAttribute('aria-pressed',on[v]?'true':'false'); apply();
    });
  });
  q.addEventListener('input',apply);
  document.addEventListener('click',function(e){
    var b=e.target.closest('button.decl'); if(!b) return;
    var open=b.getAttribute('aria-expanded')==='true';
    b.setAttribute('aria-expanded',open?'false':'true');
    document.getElementById(b.getAttribute('aria-controls')).hidden=open;
  });
  var typed=new Set();
  function typeset(sec){
    if(!sec||typed.has(sec.id)) return; typed.add(sec.id);
    try{ if(window.MathJax&&MathJax.startup&&MathJax.startup.promise){
      MathJax.startup.promise.then(function(){ return MathJax.typesetPromise([sec]); }).catch(function(){}); } }catch(e){}
  }
  typeset(document.querySelector('header.mast'));
  try{
    if('IntersectionObserver' in window){
      var io=new IntersectionObserver(function(es){
        es.forEach(function(e){ if(e.isIntersecting) typeset(e.target); });
      },{rootMargin:'900px 0px 900px 0px'});
      chaps.forEach(function(s){ io.observe(s); });
    } else { chaps.forEach(typeset); }
  }catch(e){ chaps.forEach(typeset); }
  apply();
  if(location.hash){ var el=document.querySelector(location.hash);
    if(el){ typeset(el.closest('section.chapter')); el.scrollIntoView(); } }
})();
</script>"""

    page = (head + '<div class="wrap"><main>' + mast + ''.join(ctrl) + ''.join(nav) + ''.join(body)
            + '<p class="empty" id="none" hidden>Nothing matches. Clear the search, or switch a label back on.</p>'
            + f'<p class="foot">{FOOT}</p>'
            + '</main></div>' + script)
    return page


def render_item(it):
    vid, v = it['id'], it['verdict']
    book, lean = it[BOOK_KEY], it['lean']
    label = book.get('label')
    page = book.get('page')
    # a label that already quotes the page ("§1.1, p. 7") must not have it printed twice
    label_has_page = bool(label and re.search(r'p\.\s*\d', label))
    src = ' · '.join(x for x in [html.escape(label) if label else 'no counterpart in the book',
                                 f'p.&nbsp;{page}' if page and not label_has_page else ''] if x)
    chips = ''.join(f'<span class="chip">{md(c)[3:-4] if md(c).startswith("<p>") else html.escape(c)}</span>'
                    for c in it.get('chips', []))
    decl_html, code_html = [], []
    for k, d in enumerate(it['_decls']):
        panel = f'{item_id(vid)}-d{k}'
        decl_html.append(
            f'<button class="decl" type="button" aria-expanded="false" aria-controls="{panel}">'
            f'<span class="f">{html.escape(d["path"])}&nbsp;·&nbsp;</span>'
            f'{html.escape(d["full"].removeprefix(PROJECT + "."))}</button>')
        code_html.append(
            f'<div class="code" id="{panel}" hidden><p class="where">{html.escape(lean_file(d["path"]))}, '
            f'line {d["line"]} &nbsp;·&nbsp; {html.escape(d["full"])}</p>'
            f'<pre>{html.escape(d["header"])}</pre></div>')
    diff = it.get('diff') or []
    diff_html = ('<div class="diff"><p class="dlabel">What differs</p><ul>'
                 + ''.join('<li>' + (md(d)[3:-4] if md(d).startswith('<p>') else md(d)) + '</li>' for d in diff)
                 + '</ul></div>') if diff else ''
    note = f'<p class="note">{md(book["note"])[3:-4]}</p>' if book.get('note') else ''
    searchable = html.escape(' '.join([vid, it['title'], plain(book['statement']), plain(book.get('note')),
                                       plain(lean['statement']), ' '.join(it.get('chips', [])),
                                       ' '.join(plain(d) for d in diff),
                                       ' '.join(d['name'] + ' ' + d['path'] for d in it['_decls'])]).lower(),
                             quote=True)
    return f"""<article class="item" id="{item_id(vid)}" data-v="{v}" data-s="{searchable}">
<div class="ihead"><a class="vid" href="#{item_id(vid)}">{html.escape(vid)}</a><h3>{html.escape(it['title'])}</h3>
<span class="verdict">{html.escape(VNAME[v])}</span></div>
{f'<div class="chips">{chips}</div>' if chips else ''}
<div class="cols">
<div class="col book"><p class="clabel">{BOOK_SHORT} <span class="src">{src}</span></p>{md(book['statement'])}{note}</div>
<div class="col lean"><p class="clabel">{'In the formalization' if v in ('gap', 'closed') else 'Proved in Lean'}</p>{md(lean['statement'])}
{f'<div class="decls">{"".join(decl_html)}</div>' if decl_html else ''}{''.join(code_html)}</div>
</div>{diff_html}</article>"""


def markdown_source(items):
    out = [f'# {TITLE}', '', f'*{DEK}*', '',
           'Left: the statement as the book states it. Right: the statement proved in Lean, with the '
           'hypotheses written out. Each declaration is given with its file and line.', '']
    for prefix, name, sub in CHAPTERS:
        sel = [it for it in items if chapter_of(it['id']) == prefix]
        if not sel:
            continue
        out += [f'## {name}', '', f'*{sub}*', '']
        for it in sel:
            book, lean = it[BOOK_KEY], it['lean']
            src = book.get('label') or 'no counterpart in the book'
            if book.get('page') and not re.search(r'p\.\s*\d', src):
                src += f', p. {book["page"]}'
            out += [f'### {it["id"]}. {it["title"]}', '',
                    f'*{VNAME[it["verdict"]]}*'
                    + (' · ' + ' · '.join(it['chips']) if it.get('chips') else ''), '',
                    f'**{BOOK_SHORT} ({src}).** {book["statement"]}', '']
            if book.get('note'):
                out += [f'*{book["note"]}*', '']
            out += [f'**Proved in Lean.** {lean["statement"]}', '']
            for d in it['_decls']:
                # `Test.lean` is not imported by the library, so `check_names.py` cannot see its
                # declarations; they are cited without the project prefix (its documented convention)
                full = d['full'].removeprefix(PROJECT + '.') if d['path'] == 'Test' else d['full']
                out += [f'- `{full}` — {lean_file(d["path"])}, line {d["line"]}']
            out += ['']
            if it.get('diff'):
                out += ['*What differs.*']
                out += [f'- {d}' for d in it['diff']]
                out += ['']
    return '\n'.join(out) + '\n'


def main(outdir):
    items = load()
    print(f'{len(items)} items')
    bad = validate(items)
    bad += resolve_decls(items)
    for b in bad:
        print('  PROBLEM', b)
    counts = collections.Counter(it['verdict'] for it in items)
    print('verdicts:', dict(counts))
    page = render(items)
    (outdir / OUT_HTML).write_text(page)
    (outdir / OUT_PREVIEW).write_text(
        '<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
        '</head><body>' + page + '</body></html>')
    print('html', (outdir / OUT_HTML).stat().st_size, 'bytes')
    text = markdown_source(items)
    (outdir / OUT_MD).write_text(text)
    print('markdown', len(text), 'chars ->', outdir / OUT_MD)
    return len(bad)


if __name__ == '__main__':
    where = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else EXDIR
    sys.exit(1 if main(where) else 0)
