#!/usr/bin/env python3
"""Emit #59 cards as published copies inside the repository.

A card is a *copy* of a cross-module-referenced theorem, published alongside its definition
module — the definition module keeps its API and the result also publishes as a card, which is
the FLT-export precedent the issue adopts. Nothing is removed from any definition module, so the
module tree is unchanged and no import can cycle.

In-repo form: ``LeanCategories/<owner>/Cards/<Name>.lean`` imports the definition module and
restates the result under its card name, delegating the proof to the original declaration:

    theorem <card name> := Subsets.range_ambientEquiv

which is the same statement with the proof delegated, needs no ``sorry``, and keeps repository QC
green. The platform form (``import Definitions.Def_<module>``) is derived from this by the
publisher, per decision 3.

The card set is the graph's ``theorem``-kind declarations referenced from a module other than
their own, minus generated companions, which have no source text of their own.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRAPH = ROOT / "LeanCategories/Tools/reference-graph.json"

# Generated companions of other declarations: tactic-proof auxiliaries and equation lemmas.
GENERATED = re.compile(r"(_proof_\d+|_eq_\d+|match_\d+|_sunfold|_unfold|\.eq_\d+|\.match_|\.injEq|\.inj$|_cstage|_fstage)")

HEADER = """/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

"""


def load() -> tuple[list[dict], dict[str, set[str]]]:
    rows = json.loads(GRAPH.read_text(encoding="utf-8"))
    refs_from: dict[str, set[str]] = {}
    for r in rows:
        for c in r["refs"]:
            refs_from.setdefault(c, set()).add(r["module"])
    return rows, refs_from


def card_set(rows: list[dict], refs_from: dict[str, set[str]]) -> list[dict]:
    out = []
    for r in rows:
        if r["kind"] != "theorem" or GENERATED.search(r["name"]):
            continue
        others = refs_from.get(r["name"], set()) - {r["module"]}
        if others:
            out.append({**r, "referenced_by": sorted(others)})
    return out


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def source_name(path: Path, short: str) -> str | None:
    """The declaration as written in its module (may be namespace-qualified)."""
    pat = re.compile(rf"^(?:theorem|lemma)\s+((?:\w+\.)*{re.escape(short)})\b", re.M)
    m = pat.search(path.read_text(encoding="utf-8"))
    return m.group(1) if m else None


def emit(owner: str, apply: bool) -> int:
    rows, refs_from = load()
    sel = [c for c in card_set(rows, refs_from) if c["module"].split(".")[1] == owner]
    if not sel:
        print(f"no cards in owner directory {owner}")
        return 0
    print(f"owner directory {owner}: {len(sel)} card(s)\n")
    written = 0
    for c in sorted(sel, key=lambda r: r["name"]):
        short = c["name"].rsplit(".", 1)[-1]
        src = module_path(c["module"])
        written_name = source_name(src, short)
        if written_name is None:
            print(f"  SKIP     {c['name']}: no source declaration in {src.relative_to(ROOT)}")
            continue
        card_name = c["name"].replace(".", "_")
        body = (HEADER
                + f"public import {c['module']}\n\n"
                + "/-! # Card: " + c["name"] + "\n\n"
                + "Published copy of a result from `" + c["module"] + "`. The definition module "
                  "keeps it; this file restates it under the platform card name with the proof "
                  "delegated to the original declaration.\n-/\n\n"
                + "@[expose] public section\n\n"
                + f"/-- `{c['name']}`, published as a card. -/\n"
                + f"theorem {card_name} :=\n  {written_name}\n")
        target = ROOT / f"LeanCategories/{owner}/Cards/{short}.lean"
        print(f"  CARD     {c['name']}")
        print(f"           -> {target.relative_to(ROOT)}  (theorem {card_name} := {written_name})")
        if apply:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(body, encoding="utf-8")
            written += 1
    if apply:
        print(f"\n{owner}: wrote {written} card file(s)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--owner", required=True)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    return emit(args.owner, args.apply)


if __name__ == "__main__":
    sys.exit(main())
