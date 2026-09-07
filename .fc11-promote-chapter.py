from __future__ import annotations

from collections import Counter
import json
import re
from pathlib import Path
import sys

if len(sys.argv) < 3:
    raise SystemExit('usage: .fc11-promote-chapter.py C02 "Chapter title" [search-note]')

CH = sys.argv[1]
TITLE = sys.argv[2]
SEARCH_NOTE = sys.argv[3] if len(sys.argv) > 3 else (
    'Project, pinned/current Mathlib, Mathlib history/open PRs, LeanSearch/Loogle, '
    'Reservoir/package index, broad GitHub Lean, source atlas and local reference corpora were searched.'
)

ROOT = Path('/home/dzack/gitclones/lean-categories')
SCRATCH = Path('/tmp/fc11-continuation')
UNITS = json.loads((SCRATCH / 'units.json').read_text())
DECISIONS = json.loads((SCRATCH / f'{CH.lower()}-decisions.json').read_text())

A = '12618f8abc2b4852b3da9ab65c3bc547ac4c1f19'
P = 'db584cd6d46c92f209a44c0f1c829460d327499d'
H = '71a80585ee495fc24472fd0eaffc89d94e4fd8d6'
T = '98a6bfc9f3cb4ab3a159d83858ce546d1e543c1b'
TMATHLIB = 'e21ec05048292b3de86d4cf1987e2208171a5642'
R = '47df8f51939b364e678893d54e8a3faf6ec52302'
RMATHLIB = '2fbace17aa59d5dd7d99fc4af3849722f69272df'

chapter_units = [u for u in UNITS if u['chapter'] == CH]
assert chapter_units
assert set(DECISIONS) == {str(i) for i in range(1, len(chapter_units) + 1)}

roots = {
    'A': ROOT / 'LeanCategories',
    'P': ROOT / '.lake/packages/mathlib/Mathlib',
    'T': SCRATCH / 'external/TauCeti/TauCeti',
    'R': SCRATCH / 'external/HassePrinciple/HassePrinciple',
}

def validate_positive_refs() -> None:
    errors = []
    for number, d in DECISIONS.items():
        if d['route'] == 'unmatched':
            continue
        if not d['refs']:
            errors.append(f'U{number}: empty positive refs')
            continue
        for segment in d['refs'].split(';'):
            segment = segment.strip()
            m = re.match(r'^([APTR])/([^ ]+\.lean)\s*::\s*(.+)$', segment)
            if not m:
                errors.append(f'U{number}: positive segment must be exact file :: decls: {segment!r}')
                continue
            family, rel, decls = m.groups()
            path = roots[family] / rel
            if not path.exists():
                errors.append(f'U{number}: missing {family}/{rel}')
                continue
            text = path.read_text(errors='ignore')
            for decl in map(str.strip, decls.split(',')):
                if decl.split('.')[-1] not in text:
                    errors.append(f'U{number}: declaration {decl} absent from {family}/{rel}')
    if errors:
        raise SystemExit('\n'.join(errors))

def md(s: str) -> str:
    return ' '.join(s.replace('|', r'\|').split())

def targets(refs: str) -> str:
    rendered = []
    for segment in refs.split(';'):
        family, rest = segment.strip().split('/', 1)
        rest = rest.replace(' :: ', '::')
        prefix = {'A': 'LeanCategories/', 'P': 'Mathlib/', 'T': 'TauCeti/',
                  'R': 'HassePrinciple/'}[family]
        rendered.append(f'`{prefix}{rest}`')
    return '; '.join(rendered)

def provenance(route: str) -> str:
    if route == 'mathlib':
        return f'P={P}; Apache-2.0; Lean 4.33.0'
    if route == 'project-existing':
        return f'A={A}; Apache-2.0; Lean 4.33.0'
    if route == 'reference-port':
        return f'reference source pinned in targets; Apache-2.0; source port required to Lean 4.33.0'
    if route == 'package-import':
        return 'exact package revision/license/toolchain recorded in interface comparison'
    if route == 'unmatched':
        return f'A={A}; P={P}; H={H}; full Sweep-II search N=2026-09-07'
    raise ValueError(route)

validate_positive_refs()
counts = Counter(d['route'] for d in DECISIONS.values())
chapter_no = int(CH[1:]) if CH.startswith('C') and CH[1:].isdigit() else CH
slug_title = TITLE.lower().replace('–', '-').replace('—', '-').replace('*', '')
slug_title = re.sub(r'[^a-z0-9]+', '-', slug_title).strip('-')
record_title = f'Chapter {chapter_no}. {TITLE} FC11'
record_key = f'chapter-{chapter_no}-{slug_title}-fc11'

lines = [
    f'# {record_title}', '', f'## Chapter {chapter_no}. {TITLE}', '',
    '| FC11 ID | Verdict | Route | Lean target(s) | Provenance | Interface comparison |',
    '| --- | --- | --- | --- | --- | --- |',
]
for unit in chapter_units:
    n = str(int(unit['number']))
    d = DECISIONS[n]
    verdict = md(unit['kind'])
    if d['route'] == 'unmatched':
        verdict += ' — no complete compatible owner'
        target = '—'
    else:
        target = targets(d['refs'])
    lines.append(
        f"| `{unit['id']}` | {verdict} | `{d['route']}` | {target} | "
        f"{md(provenance(d['route']))} | {md(d['comparison'])} |"
    )

chapter_path = SCRATCH / f'{CH.lower()}-chapter.md'
chapter_path.write_text('\n'.join(lines) + '\n')

unit_search = SCRATCH / 'unit-search'
statuses = []
for unit in chapter_units:
    p = unit_search / f"{unit['id']}.json"
    if p.exists():
        statuses.append(str(json.loads(p.read_text()).get('status')))
unit_search_summary = (
    f'Unit-level LeanSearch captures: {statuses.count("200")}/{len(chapter_units)} successful'
    + (f', {statuses.count("ERROR")} service errors' if statuses.count('ERROR') else '') + '.'
) if statuses else 'No per-unit LeanSearch captures were available; chapter/family semantic searches are recorded instead.'

contract = f'''# Provenance contract for FC11 {CH}

## Provenance contract for FC11 {CH}

- Canonical source block: FC11 Peters–Sterk Chapter {chapter_no}, “{TITLE}”, `{chapter_units[0]['id']}`–`{chapter_units[-1]['id']}`, {len(chapter_units)} units, exact canonical order from [[foundational-corpus-units-fc11-peters-sterk]].
- Project baseline `A={A}` (Apache-2.0, Lean 4.33.0); pinned Mathlib `P={P}` (Apache-2.0, Lean 4.33.0); current upstream Mathlib `H={H}`.
- {SEARCH_NOTE}
- {unit_search_summary}
- Strict whole-row semantics: a positive route requires an already existing complete compatible owner; partial definitions, constructors, generic ingredients, comments, axioms, or theorem fragments remain `unmatched` when substantive reconstruction would be required.
- TauCeti candidates, when used, are pinned at `{T}` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `{TMATHLIB}`) and therefore route as `reference-port`, not direct package import, unless an independently compatible package owner is recorded.
- HassePrinciple candidates, when used, are pinned at `{R}` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `{RMATHLIB}`) and likewise route as `reference-port`; declarations whose proof or required dependency remains `sorry` are not accepted as positive evidence.
- Route totals: `mathlib` {counts['mathlib']}, `project-existing` {counts['project-existing']}, `package-import` {counts['package-import']}, `reference-port` {counts['reference-port']}, `unmatched` {counts['unmatched']}.
- Negative results are scoped to the inspected revisions and dated search surfaces on 2026-09-07; they are not claims about future repository/package state.
'''
contract_path = SCRATCH / f'{CH.lower()}-contract.md'
contract_path.write_text(contract)

meta = {
    'chapter': CH, 'chapter_number': chapter_no, 'title': TITLE,
    'record_title': record_title, 'record_key': record_key,
    'chapter_path': str(chapter_path), 'contract_path': str(contract_path),
    'counts': dict(counts), 'units': len(chapter_units),
}
(SCRATCH / f'{CH.lower()}-promotion-meta.json').write_text(json.dumps(meta, indent=2))
print(json.dumps(meta, indent=2))
