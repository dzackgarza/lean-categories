#!/usr/bin/env python3
"""Extract #59 cards into the repository's publishable form.

Reads ``LeanCategories/Tools/reference-graph.json`` and, for a chosen owner directory, emits one
card file per cross-module-referenced theorem:

    LeanCategories/<owner>/Cards/<Name>.lean      -- one theorem, in platform form

Platform form, per decision 3 of issue #59:

* the card keeps its dotted name, and lives at ``Theorems.Thm_<dotted name with dots as
  underscores>`` on the platform;
* imports of other repository modules rewrite to ``import Definitions.Def_<module>`` (definition
  modules) or ``import Theorems.Thm_<card>`` (cards it uses); Mathlib and Lean imports pass
  through untouched;
* the module system is lowered (``module`` dropped, ``public import`` → ``import``,
  ``public``/``@[expose]`` dropped), because the platform's support for it is unverified
  (transformation 2).

Transformation 4's removal step is gated by a check this script performs rather than assumes: a
theorem that its *own* module also references cannot move out, because the definition module would
then have to import its own card and the import graph would cycle. Such cards are reported as
blocked, with the in-module referencing lines, and are not moved.

Deterministic output: cards are emitted in sorted order and the file content is a pure function of
the source text, so re-running on an unchanged tree produces no diff.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRAPH = ROOT / "LeanCategories/Tools/reference-graph.json"

HEADER = """/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
"""


def load_graph() -> tuple[list[dict], dict[str, set[str]]]:
    rows = json.loads(GRAPH.read_text(encoding="utf-8"))
    refs_from: dict[str, set[str]] = {}
    for r in rows:
        for c in r["refs"]:
            refs_from.setdefault(c, set()).add(r["module"])
    return rows, refs_from


def cards(rows: list[dict], refs_from: dict[str, set[str]]) -> list[dict]:
    out = []
    for r in rows:
        if r["kind"] != "theorem":
            continue
        others = refs_from.get(r["name"], set()) - {r["module"]}
        if others:
            out.append({**r, "referenced_by": sorted(others)})
    return out


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def declaration_text(path: Path, short_name: str) -> tuple[str, list[str]] | None:
    """The declaration's source text, plus any attributes immediately above it."""
    lines = path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short_name)}\b")
    for i, line in enumerate(lines):
        if pat.match(line):
            start = i
            while start > 0 and (lines[start - 1].startswith("@[")
                                 or lines[start - 1].lstrip().startswith("--")):
                start -= 1
            end = i
            while end < len(lines) and lines[end].strip():
                end += 1
            return "\n".join(lines[start:end]), lines
    return None


def in_module_uses(lines: list[str], short_name: str, decl_start: int) -> list[int]:
    """1-based line numbers in the same file that mention the name outside its own declaration."""
    # a qualified use (`Subsets.range_ambientEquiv`) counts as an in-module use, so the pattern
    # allows namespace prefixes but forbids a preceding identifier character
    pat = re.compile(rf"(?<![\w])(?:\w+\.)*{re.escape(short_name)}(?![\w'])")
    return [i + 1 for i, l in enumerate(lines)
            if i != decl_start and pat.search(l)]


def card_imports(module: str, uses: set[str]) -> list[str]:
    idx = 0
    for f in (ROOT / "LeanCategories/All.lean", ROOT / "LeanCategories/Catalogue.lean"):
        if f.exists():
            idx += 0
    imports = [f"import Definitions.Def_{module.replace('.', '_')}"]
    for u in sorted(uses):
        imports.append(f"import Theorems.Thm_{u.replace('.', '_')}")
    return imports


def lower(text: str) -> str:
    text = re.sub(r"^module\s*$\n?", "", text, flags=re.M)
    text = re.sub(r"^(?:public |private )?import ", "import ", text, flags=re.M)
    text = re.sub(r"^public section\s*$", "section", text, flags=re.M)
    return text.replace("public ", "").replace("@[expose] ", "")


def emit(owner: str, apply: bool) -> int:
    rows, refs_from = load_graph()
    sel = [c for c in cards(rows, refs_from)
           if c["module"].split(".")[1] == owner]
    if not sel:
        print(f"no cards in owner directory {owner}")
        return 0

    print(f"owner directory {owner}: {len(sel)} card(s)\n")
    done = blocked = 0
    for c in sorted(sel, key=lambda r: r["name"]):
        short = c["name"].rsplit(".", 1)[-1]
        src = module_path(c["module"])
        found = declaration_text(src, short)
        if found is None:
            print(f"  {c['name']}: MISSING SOURCE TEXT in {src.relative_to(ROOT)}")
            continue
        text, lines = found
        decl_line = next(i for i, l in enumerate(lines)
                         if re.match(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b", l))
        internal = in_module_uses(lines, short, decl_line)
        # cards this theorem's proof references
        uses = {u for u in c["refs"]
                if any(x["name"] == u and x["kind"] == "theorem" and
                       (refs_from.get(u, set()) - {x["module"]}) for x in rows)}
        if internal:
            blocked += 1
            print(f"  BLOCKED  {c['name']}")
            print(f"           also referenced inside its own module at "
                  f"{src.relative_to(ROOT)}:{','.join(map(str, internal))}")
            print(f"           moving it would make that module import its own card")
            continue
        done += 1
        imports = card_imports(c["module"], uses)
        body = lower(HEADER + "\n" + "\n".join(imports) + "\n\n" + text + "\n")
        target = ROOT / f"LeanCategories/{owner}/Cards/{short}.lean"
        print(f"  OK       {c['name']}")
        print(f"           -> {target.relative_to(ROOT)}")
        for i in imports:
            print(f"           {i}")
        if apply:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(body, encoding="utf-8")
    print(f"\n{owner}: {done} emittable, {blocked} blocked")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--owner", required=True, help="owner directory, e.g. Foundation")
    ap.add_argument("--apply", action="store_true", help="write the card files")
    args = ap.parse_args()
    return emit(args.owner, args.apply)


if __name__ == "__main__":
    sys.exit(main())
