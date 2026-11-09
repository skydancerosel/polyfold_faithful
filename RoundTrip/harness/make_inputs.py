"""Regenerate the round-trip inputs under $RT_DIR from Exposition/cmp/*.json.

blind/<ID>.md  the book's statement only (given to the blind formalizer)
keys/<ID>.json the full comparison item, verdict included (never shown to blind formalizers or provers)
decls/<ID>.txt the item's declaration names (given to provers, without the verdict)
The vocabulary dump: `lake env lean RoundTrip/harness/Vocab.lean` writes $RT_DIR/vocab.md.
"""
import json, glob, os
R = os.environ.get('RT_DIR', '/tmp/rt')
for d in ('blind', 'keys', 'decls'):
    os.makedirs(f'{R}/{d}', exist_ok=True)
here = os.path.dirname(os.path.abspath(__file__))
for f in sorted(glob.glob(os.path.join(here, '../../Exposition/cmp/*.json'))):
    for e in json.load(open(f))['items']:
        i = e['id'].replace('.', '_'); b = e['book']
        # Part I (Chapters 1-6) is quoted from the 2014 preprint; Part II has no preprint: Chapters
        # 7-8 are quoted from the 2017 book (arXiv 1707.08941), Chapters 9-11 from the Springer 2021
        # book (audited 2026-11-08; their labels give the 2021 numbers, the 2017 ones in parentheses), as are
        # the items of Chapters 7-8 new in the 2021 edition.
        n = e['id'][1:].split('.')[0]
        src = ("*Polyfold and Fredholm Theory* (Springer 2021), Part II"
               if n.isdigit() and (int(n) >= 9 or (int(n) >= 7 and '2021 edition' in b['label']))
               else "*Polyfold and Fredholm Theory* (2017 book, arXiv 1707.08941), Part II"
               if n.isdigit() and int(n) >= 7
               else "*Polyfold and Fredholm Theory I* (preprint, arXiv 1407.3185)")
        open(f'{R}/blind/{i}.md', 'w').write(
            f"# {e['id']}: {e['title']}\n\nHofer–Wysocki–Zehnder, {src}, {b['label']}.\n\n"
            f"{b['statement']}\n")
        json.dump(e, open(f'{R}/keys/{i}.json', 'w'), ensure_ascii=False, indent=1)
        open(f'{R}/decls/{i}.txt', 'w').write(
            '\n'.join(d.split('·')[-1].strip() for d in e['lean']['decls']) + '\n')
