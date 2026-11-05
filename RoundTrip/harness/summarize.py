"""Summarize the round-trip records RoundTrip/Items/*.json as markdown tables.

Usage: RT_DIR=<scratch> python3 RoundTrip/harness/summarize.py [--rows]
Needs $RT_DIR/keys/ (from make_inputs.py) for the comparison's verdicts.
"""
import json, glob, os, sys, collections, re

R = os.environ.get('RT_DIR', '/tmp/rt')
here = os.path.dirname(os.path.abspath(__file__))
exp = {'same': 'equivalent', 'explicit': 'equivalent', 'restated': 'equivalent',
       'stronger': 'A_stronger', 'narrower': 'A_narrower'}
rows = []
for f in sorted(glob.glob(os.path.join(here, '../Items/*.json')),
                key=lambda p: [int(x) for x in re.findall(r'\d+', os.path.basename(p))]):
    r = json.load(open(f)); i = os.path.basename(f)[:-5]
    k = json.load(open(f'{R}/keys/{i}.json'))
    uh = r.get('uses_hypothesis') or {}
    def real(d):
        v = uh.get(d, True)
        return r.get(d) == 'proved' and v is not False and v != 'false'
    ab, ba = real('A_to_B'), real('B_to_A')
    if r.get('not_B') or r.get('A_to_B') == 'false':
        proved = 'B false'
    else:
        proved = ('equivalent' if ab and ba else 'A ⇒ B only' if ab else 'B ⇒ A only' if ba
                  else 'neither')
    rows.append(dict(id=i, ch=i.split('_')[0], title=k['title'], verdict=k['verdict'],
                     rel=r.get('relation'), proved=proved, effort=r.get('effort_only'),
                     intended=bool(r.get('intended')), why=r.get('why', '')))

def table(key, cols, rowsel):
    t = collections.Counter((rowsel(x), x[key]) for x in rows)
    names = sorted({rowsel(x) for x in rows}, key=lambda s: (len(s), s))
    out = ['| | ' + ' | '.join(cols) + ' | n |', '|---|' + '---|' * (len(cols) + 1)]
    for n in names:
        c = [t[(n, col)] for col in cols]
        out.append(f'| {n} | ' + ' | '.join(map(str, c)) + f' | {sum(c)} |')
    return '\n'.join(out)

P = ['equivalent', 'A ⇒ B only', 'B ⇒ A only', 'neither', 'B false']
C = ['equivalent', 'A_stronger', 'A_narrower', 'incomparable']
print(f'{len(rows)} items\n')
print('Proved directions (vacuous directions not counted), by chapter:\n')
print(table('proved', P, lambda x: x['ch']))
print('\nProved directions by verdict:\n')
print(table('proved', P, lambda x: x['verdict']))
print("\nProvers' judgement of content, by verdict:\n")
print(table('rel', C, lambda x: x['verdict']))
m = collections.Counter('match' if x['rel'] == exp.get(x['verdict']) else
                        'partial' if x['rel'] == 'incomparable' and x['verdict'] in ('stronger', 'narrower')
                        else 'mismatch' for x in rows)
print(f'\nAgainst the verdict: {dict(m)}')
if '--rows' in sys.argv:
    print('\n| item | verdict | proved | content | why |\n|---|---|---|---|---|')
    for x in rows:
        w = x['why'].replace('|', '/').replace('\n', ' ')
        print(f"| {x['id']} | {x['verdict']} | {x['proved']} | {x['rel']} | {w[:300]} |")
