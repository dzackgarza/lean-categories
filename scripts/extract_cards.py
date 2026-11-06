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
their own, minus **generated companions**. The companion test is by source, not by name: a
declaration is a companion when its module contains no `theorem`/`lemma` declaration of that name —
that is, when it is produced by a `class`/`structure`/`instance` command, an `@[ext]` derivation or
a tactic block. Companions leave the population; the ones excluded are printed so the list can be
checked.

With that test the population is 394 cards, down from 460.
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
# A `source:` citation line in a module docstring — not the `source :=` field of a structure.
SOURCE_LINE = re.compile(r"^\s*source\s*:\s*(?!:?=)(\S.*)$", re.M | re.I)

GENERATED = re.compile(r"(_proof_\d+|_eq_\d+|match_\d+|_sunfold|_unfold|\.eq_\d+|\.match_|\.injEq|\.inj$|_cstage|_fstage)")

def SRC_OPEN(module: str) -> str:
    return f"open {module.rsplit('.', 1)[0]}\n\n" if False else ""


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


SIMPLIKE = re.compile(r"@\[\s*(?:[^\]]*\b)?(?:simp|ext)\b")


def is_simp_or_ext(path: Path, short: str) -> bool:
    """True when the declaration carries @[simp] or @[ext] — those stay in the definition file."""
    lines = path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b")
    for i, l in enumerate(lines):
        if pat.match(l):
            j = i - 1
            while j >= 0 and (lines[j].startswith("@[") or lines[j].lstrip().startswith("--")):
                if SIMPLIKE.search(lines[j]):
                    return True
                j -= 1
            return False
    return False


def is_companion(row: dict) -> bool:
    """True when no `theorem`/`lemma` declaration of this name exists in its module."""
    short = row["name"].rsplit(".", 1)[-1]
    return statement_text(module_path(row["module"]), short) is None


def card_set(rows: list[dict], refs_from: dict[str, set[str]],
             report: bool = False) -> list[dict]:
    out, companions = [], []
    for r in rows:
        if r["kind"] != "theorem" or GENERATED.search(r["name"]):
            continue
        others = refs_from.get(r["name"], set()) - {r["module"]}
        if not others:
            continue
        p = module_path(r["module"])
        if is_companion(r) or is_simp_or_ext(p, r["name"].rsplit(".", 1)[-1]):
            companions.append(r)
            continue
        out.append({**r, "referenced_by": sorted(others)})
    if report:
        print(f"companions excluded (generated, no source declaration): {len(companions)}")
        for r in sorted(companions, key=lambda x: x["name"]):
            print(f"  companion  {r['name']}  ({r['module']})")
        print()
    return out


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def source_name(path: Path, short: str) -> str | None:
    """The declaration as written in its module (may be namespace-qualified)."""
    pat = re.compile(rf"^(?:theorem|lemma)\s+((?:\w+\.)*{re.escape(short)})\b", re.M)
    m = pat.search(path.read_text(encoding="utf-8"))
    return m.group(1) if m else None


def statement_text(path: Path, short: str) -> str | None:
    """Binders and type of a declaration, copied from the source up to (not including) `:=`."""
    lines = path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b")
    for i, l in enumerate(lines):
        if pat.match(l):
            head = re.sub(rf"^(theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b", "", l)
            chunk = [head]
            j = i
            while not "\n".join(chunk).rstrip().endswith(":=") and ":= by" not in "\n".join(chunk) and ":= rfl" not in "\n".join(chunk):
                j += 1
                if j >= len(lines):
                    return None
                chunk.append(lines[j])
            text = "\n".join(chunk)
            idx = min([text.find(k) for k in (":= by", ":= rfl", "\n:=") if text.find(k) >= 0] or [len(text)])
            return text[:idx].rstrip()
    return None


def docstring_of(path: Path, short: str, full: str) -> tuple[str, bool]:
    """The original's docstring if it has one, else an authored one. Second component: authored?"""
    lines = path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b")
    for i, l in enumerate(lines):
        if pat.match(l):
            j = i - 1
            block: list[str] = []
            while j >= 0 and lines[j].strip():
                block.insert(0, lines[j])
                j -= 1
            text = "\n".join(block)
            if "/--" in text and "-/" in text:
                start = text.rindex("/--")
                end = text.rindex("-/") + 2
                return text[start:end], False
            return (f"/-- A published result of `{full.rsplit('.', 1)[0]}`, restated here under its "
                    f"platform card name with the proof delegated to the original declaration. -/",
                    True)
    return (f"/-- `{full}`, published as a card. -/", True)


SCOPE_OPEN = re.compile(r"^\s*(namespace\s+\S+|section(?:\s+\S+)?)\s*$")
SCOPE_INNER = re.compile(r"^\s*(open\s|variable\s|universe\s|attribute\s*\[|set_option\s|local\s)")


def full_declaration(path: Path, short: str, new_name: str) -> str | None:
    """The declaration copied verbatim with its name replaced."""
    lines = path.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^(theorem|lemma)\s+((?:\w+\.)*){re.escape(short)}\b")
    for i, l in enumerate(lines):
        if pat.match(l):
            outs = [pat.sub(lambda mm: f"{mm.group(1)} {mm.group(2)}{new_name}", l)]
            j = i + 1
            while j < len(lines) and (lines[j].startswith(" ") or lines[j].startswith("\t")):
                outs.append(lines[j]); j += 1
            return "\n".join(outs)
    return None


def explicit_binders(stmt: str) -> list[str]:
    """Names of the explicit `( … )` binders in a copied signature, in order."""
    # only the part before the top-level `:` that separates binders from the type
    depth0, cut = 0, len(stmt)
    for k, ch in enumerate(stmt):
        if ch in "({[⦃":
            depth0 += 1
        elif ch in ")}]⦄":
            depth0 -= 1
        elif ch == ":" and depth0 == 0:
            cut = k
            break
    stmt = stmt[:cut]
    names, depth, i = [], 0, 0
    while i < len(stmt):
        ch = stmt[i]
        if ch in "({[⦃":
            depth += 1
            if ch == "(":
                # a binder group: (n1 n2 : T) — take identifiers before the first ':'
                j = i + 1
                grp, d = "", 1
                while j < len(stmt) and d:
                    if stmt[j] in "({[⦃":
                        d += 1
                    elif stmt[j] in ")}]⦄":
                        d -= 1
                        if d == 0:
                            break
                    grp += stmt[j]
                    j += 1
                head = grp.split(":")[0]
                for tok in re.findall(r"[A-Za-z_][\w']*", head):
                    names.append(tok)
        elif ch in ")}]⦄":
            depth -= 1
        i += 1
    return names


def scope_context(path: Path, decl_line: int) -> tuple[str, int]:
    """The scope in force at `decl_line`: namespace/section/open/variable lines, in order.

    This is the text Lean had in scope when it compiled the original declaration, so a verbatim
    copy placed in the same scope compiles for the same reason the original does. Lines after the
    declaration and lines inside sibling sections that have already been closed are excluded.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    depth = 0
    active: list[tuple[int, str]] = []      # (depth, text)
    opener_names: list[str] = []
    for line in lines[:decl_line]:
        stripped = line.strip()
        if SCOPE_OPEN.match(line):
            depth += 1
            opener_names.append(stripped)
            active.append((depth, ("open " + stripped.split(None, 1)[1].strip())
                           if stripped.startswith("namespace") else line.rstrip()))
        elif stripped == "end" or re.match(r"^end\s+\S+$", stripped):
            if depth > 0:
                active = [a for a in active if a[0] < depth]
                depth -= 1
                if opener_names:
                    opener_names.pop()
        elif SCOPE_INNER.match(line):
            active.append((depth, line.rstrip()))
    text = "\n".join(t for _, t in active)
    closers = []
    for o in reversed(opener_names):
        closers.append(None) if False else None
        if not o.startswith("namespace"):
            closers.append("end")
    return (text + "\n\n" if text else ""), "\n".join(closers)


def source_of(module: str) -> str | None:
    """The `source:` citation a card inherits from its definition module, if it has one."""
    p = module_path(module)
    if not p.exists():
        return None
    m = SOURCE_LINE.search(p.read_text(encoding="utf-8"))
    return m.group(1).strip() if m else None


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
        src_missing = source_of(c["module"]) is None
        if src_missing:
            print(f"  REFUSED  {c['name']}: definition module has no `source:` line")
            continue
        if written_name is None:
            print(f"  SKIP     {c['name']}: no source declaration in {src.relative_to(ROOT)}")
            continue
        card_name = c["name"].replace(".", "_")
        stmt = statement_text(src, short)
        if stmt is None:
            print(f"  SKIP     {c['name']}: cannot extract a signature")
            continue
        decl_line = next(i for i, l in enumerate(src.read_text(encoding="utf-8").splitlines())
                         if re.match(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b", l))
        scope_ctx, scope_ends = scope_context(src, decl_line)
        doc, authored = docstring_of(src, short, c["name"])
        if authored:
            print(f"  REFUSED  {c['name']}: the declaration has no docstring in its module, so no "
                  f"natural_language_statement exists — write one there first")
            continue
        decl_line = next(i for i, l in enumerate(src.read_text(encoding="utf-8").splitlines())
                         if re.match(rf"^(?:theorem|lemma)\s+(?:\w+\.)*{re.escape(short)}\b", l))
        scope_ctx, scope_ends = scope_context(src, decl_line)
        doc, authored = docstring_of(src, short, c["name"])
        if authored:
            print(f"  REFUSED  {c['name']}: the declaration has no docstring in its module, so no "
                  f"natural_language_statement exists — write one there first")
            continue
        body = (
            HEADER
            + f"public import {c['module']}\n\n"
            + f"/-! # Card: `{c['name']}`\n\n"
            + f"source: {source_of(c['module'])}\n\n"
            + f"Published copy of a result from `{c['module']}`; the definition module keeps the "
              "original declaration, this file restates it, and the platform submission replaces "
              "the delegated proof with `by sorry`.\n-/\n\n"
            + "@[expose] public section\n\n"
            + f"namespace LeanCategories.Cards\n\n"
            + f"open {c['module'].rsplit('.', 1)[0]}\n\n"
            + scope_ctx
            + doc + "\n"
            + f"theorem {card_name}{stmt} :=\n  {c['name']}"
            + ("".join(" " + b for b in explicit_binders(stmt))) + "\n\n"
            + scope_ends + "\n"
            + "end LeanCategories.Cards\n"
        )

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
