#!/usr/bin/env python3
"""The `realization-stub-audit` population: `[realized]` rows not yet shown to construct.

A row leaves the population only through `[construction-confirmed: Name]`, where `Name` is a
declaration in one of the row's Lean files that *constructs* the row's object: a `def`,
`abbrev`, `structure`, `class`, `inductive` or `instance` that is not a predicate. Rejected:
a name beginning with `Is`, and any declaration whose type is `Prop` (a graph or property of a
supplied map is not the map). A bare `[construction-confirmed]` marker proves nothing and keeps
the row in the population. Prints one line per open row; acceptance is empty output.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNIT = re.compile(r"^\|\s*`([A-Z0-9]+-[A-Z0-9-]+)`")
NET = re.compile(r"supplied|candidate|caller|result obligation|without proving|as (a )?hypothes", re.IGNORECASE)
MARK = re.compile(r"\[construction-confirmed:\s*`?([\w.']+)`?\s*\]")
LEAN = re.compile(r"LeanCategories/[\w/]+\.lean")
DECL = r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(def|abbrev|structure|class|inductive|instance)\s+{name}\b"


def header(text: str, start: int) -> str:
    """The declaration's signature: from its keyword to the first `:=` or `where`."""
    rest = text[start:]
    end = min((i for i in (rest.find(":="), rest.find(" where")) if i >= 0), default=len(rest))
    return rest[:end]


def verdict(row: str) -> str | None:
    """None when the row is validly confirmed, else why it is still open."""
    mark = MARK.search(row)
    if not mark:
        return "no named constructing declaration"
    name = mark.group(1)
    short = name.rsplit(".", 1)[-1]
    if short.startswith(("Is", "is_")):
        return f"{name} is a predicate, not a construction"
    pattern = re.compile(DECL.format(name=re.escape(short)), re.MULTILINE)
    for rel in dict.fromkeys(LEAN.findall(row)):
        path = ROOT / rel
        if not path.exists():
            continue
        text = path.read_text()
        match = pattern.search(text)
        if not match:
            continue
        if re.search(r":\s*Prop\s*$", header(text, match.start()).strip()):
            return f"{name} is Prop-valued, not a construction"
        return None
    return f"{name} is not declared in the row's Lean files"


def main() -> int:
    open_rows = 0
    for md in sorted((ROOT / "corpus").glob("*.md")):
        for line in md.read_text().splitlines():
            unit = UNIT.match(line)
            if not unit or "[realized]" not in line:
                continue
            if not NET.search(line) and "[construction-confirmed" not in line:
                continue
            why = verdict(line)
            if why:
                open_rows += 1
                print(f"{unit.group(1)}\t{md.name}\t{why}")
    print(f"{open_rows} open", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
