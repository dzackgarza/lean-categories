from __future__ import annotations

from collections import Counter
import json
import re
from pathlib import Path

ROOT = Path('/home/dzack/gitclones/lean-categories')
SCRATCH = Path('/tmp/fc11-continuation')
UNITS = json.loads((SCRATCH / 'units.json').read_text())
DECISIONS = json.loads((SCRATCH / 'c01-decisions.json').read_text())

A = '12618f8abc2b4852b3da9ab65c3bc547ac4c1f19'
P = 'db584cd6d46c92f209a44c0f1c829460d327499d'
H = '71a80585ee495fc24472fd0eaffc89d94e4fd8d6'
T = '98a6bfc9f3cb4ab3a159d83858ce546d1e543c1b'
TMATHLIB = 'e21ec05048292b3de86d4cf1987e2208171a5642'
FCONJ = 'b123bb89b5978ae6b648159e430c4e4dce161b97'

chapter_units = [u for u in UNITS if u['chapter'] == 'C01']
assert len(chapter_units) == 155
assert set(DECISIONS) == {str(i) for i in range(1, 156)}

roots = {
    'A': ROOT / 'LeanCategories',
    'P': ROOT / '.lake/packages/mathlib/Mathlib',
    'T': SCRATCH / 'external/TauCeti/TauCeti',
}

def validate_positive_refs() -> None:
    errors: list[str] = []
    for number, decision in DECISIONS.items():
        if decision['route'] == 'unmatched':
            continue
        refs = decision['refs']
        if not refs:
            errors.append(f'U{number}: empty positive target')
            continue
        for segment in refs.split(';'):
            segment = segment.strip()
            match = re.match(r'^([APT])/([^ ]+\.lean)\s*::\s*(.+)$', segment)
            if not match:
                errors.append(f'U{number}: non-exact positive segment {segment!r}')
                continue
            family, rel, decls = match.groups()
            path = roots[family] / rel
            if not path.exists():
                errors.append(f'U{number}: missing {family}/{rel}')
                continue
            text = path.read_text(errors='ignore')
            for decl in (d.strip() for d in decls.split(',')):
                leaf = decl.split('.')[-1]
                if leaf not in text:
                    errors.append(f'U{number}: declaration {decl} not found in {family}/{rel}')
    if errors:
        raise SystemExit('\n'.join(errors))

def md(s: str) -> str:
    return ' '.join(s.replace('|', r'\|').split())

def target_text(refs: str) -> str:
    rendered = []
    for segment in refs.split(';'):
        segment = segment.strip()
        family, rest = segment.split('/', 1)
        rest = rest.replace(' :: ', '::')
        prefix = {'A': 'LeanCategories/', 'P': 'Mathlib/', 'T': 'TauCeti/'}[family]
        rendered.append(f'`{prefix}{rest}`')
    return '; '.join(rendered)

def provenance(route: str) -> str:
    if route == 'mathlib':
        return f'P={P}; Apache-2.0; Lean 4.33.0'
    if route == 'project-existing':
        return f'A={A}; Apache-2.0; Lean 4.33.0'
    if route == 'reference-port':
        return (
            f'TauCeti@{T}; Apache-2.0; Lean 4.34.0-rc2; '
            f'Mathlib {TMATHLIB}; source port required for project Lean 4.33.0'
        )
    if route == 'unmatched':
        return (
            f'A={A}; P={P}; H={H}; project/Mathlib/history/open-PR/'
            'package/LeanSearch/Loogle/Reservoir/GitHub/reference search 2026-09-07'
        )
    raise ValueError(route)

validate_positive_refs()

lines = [
    '# Chapter 1. Symmetric and Quadratic Forms, an Overview FC11',
    '',
    '## Chapter 1. Symmetric and Quadratic Forms, an Overview',
    '',
    '| FC11 ID | Verdict | Route | Lean target(s) | Provenance | Interface comparison |',
    '| --- | --- | --- | --- | --- | --- |',
]

for unit in chapter_units:
    number = str(int(unit['number']))
    decision = DECISIONS[number]
    route = decision['route']
    verdict = md(unit['kind'])
    if route == 'unmatched':
        verdict += ' — no complete compatible owner'
        targets = '—'
    else:
        targets = target_text(decision['refs'])
    lines.append(
        f"| `{unit['id']}` | {verdict} | `{route}` | {targets} | "
        f"{md(provenance(route))} | {md(decision['comparison'])} |"
    )

(SCRATCH / 'c01-chapter.md').write_text('\n'.join(lines) + '\n')

counts = Counter(d['route'] for d in DECISIONS.values())
contract = f'''# Provenance contract for FC11 C01

## Provenance contract for FC11 C01

- Canonical source block: FC11 Peters–Sterk Chapter 1, “Symmetric and Quadratic Forms, an Overview”, `FC11-C01-U001`–`FC11-C01-U155`, 155 units, in exact canonical order from [[foundational-corpus-units-fc11-peters-sterk]].
- Project code baseline: `A={A}` (Apache-2.0, Lean 4.33.0). No project Lean source changed while this chapter was audited.
- Pinned Mathlib: `P={P}` (Apache-2.0, Lean 4.33.0). Current upstream Mathlib source was checked at `H={H}`. Targeted Mathlib history was inspected from the local full Git checkout; open-PR searches included the form/lattice families and found, among others, PR #42719 on totally isotropic subspaces, which does not close the unmatched Witt/lattice bundles.
- Search services: dated LeanSearch query captures cover linear/symmetric/quadratic forms, integral lattices, primitivity, index/discriminant, parity, reflections, Witt theory, dual/discriminant forms, gluing, local/genus/Hasse theory, dyadic forms, finiteness/Hermite, Nikulin/Niemeier, mass and theta-series families. Loogle captures cover orthogonal, discriminant, primitive/saturated, reflective, Witt, unimodular, Hermite, genus and theta vocabulary.
- Package discovery: Reservoir application/search data were captured and inspected. The local formalization-source atlas was checked across all registered sources, including `formal-conjectures@{FCONJ}`. Broad GitHub Lean code search captures cover bilinear/quadratic forms, primitive lattices, reflections, discriminant forms, overlattices, dyadic forms, Nikulin, Witt decomposition, Niemeier and Hermite families.
- Reference-port source used by three rows: `TauCeti@{T}` (Apache-2.0), Lean 4.34.0-rc2 with Mathlib `{TMATHLIB}`. Its integral-lattice index, overlattice/isotropic-subgroup, orthogonal-quotient and naturality declarations are mathematically compatible but require a source port to the project toolchain, so they are `reference-port`, not `package-import`.
- Strict whole-row semantics were used. A row is positive only when the cited existing declarations cover the full source unit without a substantive reconstruction. Partial ingredients remain `unmatched`; the rational-discriminant/binary-form remark was explicitly demoted on that basis during verification.
- Route totals for C01: `mathlib` {counts['mathlib']}, `project-existing` {counts['project-existing']}, `package-import` {counts['package-import']}, `reference-port` {counts['reference-port']}, `unmatched` {counts['unmatched']}.
- Negative result scope: every `unmatched` row records `N=2026-09-07` through its provenance field. The negative result applies only to the inspected revisions/search surfaces above and is not a claim about future Mathlib/project/package state.
'''
(SCRATCH / 'c01-contract.md').write_text(contract)

parent = f'''# FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping

Status: **Sweep II in progress.** Whole-source claim adopted on 2026-09-07 by the continuation session after the prior FC11 worker stopped. C01 is complete; C02–C21 and Appendices A–C remain in this claim and will be processed without releasing the source.

Canonical catalogue: [[foundational-corpus-units-fc11-peters-sterk|FC11 Peters–Sterk unit catalogue]].

Pinned project baseline for C01: Mathlib `{P}` on Lean 4.33.0; project `{A}`. Current upstream Mathlib searched at `{H}`. Rows use exactly one of `mathlib`, `project-existing`, `package-import`, `reference-port`, `unmatched`, under strict whole-row semantics.

## Promoted chapter records

- [[provenance-contract-for-fc11-c01|Provenance contract for FC11 C01]]
- [[chapter-1-symmetric-and-quadratic-forms-an-overview-fc11|Chapter 1. Symmetric and Quadratic Forms, an Overview FC11]]
'''
(SCRATCH / 'parent-c01.md').write_text(parent)

print('validated positive declarations')
print('route totals', dict(counts))
print('chapter', SCRATCH / 'c01-chapter.md')
print('contract', SCRATCH / 'c01-contract.md')
print('parent', SCRATCH / 'parent-c01.md')
