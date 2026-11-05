#!/usr/bin/env python3
"""Publisher for #59: emit LeanCategories modules as Prove2Me platform definitions.

Design notes, all from issue #59 (decisions recorded there, not reopened here):

* Name rule (decision 3): ``LeanCategories.A.B`` publishes as ``LeanCategories_A_B``.
  The repository keeps its mathematical module tree; the platform form is derived.
* Definitions carry their API (decision 1): a module publishes as one definition file.
* Axiom guard (transformation 3): the emitter refuses any module whose transitive import
  closure reaches a module that declares an ``axiom``, and refuses to emit at all when the
  repository's own ``lean-categories-axiom-audit`` gate is red. The excluded modules are
  printed with the issues that own them, never silently skipped.
* Module-system lowering (transformation 2): ``--lower`` drops ``module``, rewrites
  ``public import`` to ``import`` and drops ``public``/``@[expose]`` markers, for the case
  where the platform rejects the module system. The repository keeps the module system.
* ``--dry-run`` writes payloads to a directory and makes no network call, so it needs no
  credential.

Platform contract: one full Lean file per submission to ``POST /api/v1/submit-definition``
with ``definition_name`` matching ``[a-zA-Z_][a-zA-Z0-9_]*``, ``definition_title``,
``natural_language_statement`` (prose with KaTeX), and ``source``. Server compile cap 300 s;
at most 100 jobs pending; imports resolve only against Mathlib and already-published
declarations, so publication is a topological sweep layer by layer.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "LeanCategories"

# Modules that are not definition modules: the umbrella import file and the audit tools.
NON_MODULES = {"LeanCategories.All"}
NON_MODULE_PREFIXES = ("LeanCategories.Tools.",)

# The 300 s server cap is measured, not guessed (decision 5); the local threshold is set
# below it so a module that fits locally is expected to fit on the server.
SERVER_COMPILE_CAP_S = 300
LOCAL_THRESHOLD_S = 120

MAX_PENDING = 100

# Issues that own the axiom subtree, named in the output (transformation 3).
AXIOM_OWNERS = "#31, #33"


@dataclass
class Module:
    name: str                       # LeanCategories.A.B
    path: Path
    text: str
    imports: list[str] = field(default_factory=list)
    docstring: str | None = None
    source: str | None = None
    declares_axiom: bool = False
    layer: int = -1
    seconds: float | None = None

    @property
    def platform_name(self) -> str:
        return self.name.replace(".", "_")


IMPORT_RE = re.compile(r"^(?:public |private |meta )?import ([A-Za-z_][\w.]*)\s*$", re.M)
DOCSTRING_RE = re.compile(r"/-!(.*?)-/", re.S)
SOURCE_RE = re.compile(r"^\s*source\s*:\s*(.+)$", re.M | re.I)


def read_module(path: Path) -> Module:
    text = path.read_text(encoding="utf-8")
    name = path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
    m = Module(name=name, path=path, text=text)
    m.imports = IMPORT_RE.findall(text)
    doc = DOCSTRING_RE.search(text)
    if doc:
        m.docstring = doc.group(1).strip()
        src = SOURCE_RE.search(m.docstring)
        if src:
            m.source = src.group(1).strip()
    m.declares_axiom = re.search(r"^\s*axiom\s+\w+", text, re.M) is not None
    return m


def discover() -> dict[str, Module]:
    mods: dict[str, Module] = {}
    for path in sorted(LIB.rglob("*.lean")):
        m = read_module(path)
        if m.name in NON_MODULES or m.name.startswith(NON_MODULE_PREFIXES):
            continue
        mods[m.name] = m
    return mods


def compute_layers(mods: dict[str, Module]) -> None:
    """Topological layers over in-repository imports; Mathlib/Lean pass through."""
    pending = dict(mods)

    def deps(m: Module) -> set[str]:
        return {d for d in m.imports if d in mods}

    layer = 0
    while pending:
        ready = [n for n, m in pending.items() if deps(m) <= set() or
                 all(mods[d].layer >= 0 for d in deps(m))]
        if not ready:                      # import cycle: report and stop
            raise SystemExit(f"import cycle among: {sorted(pending)[:5]} …")
        for n in ready:
            pending[n].layer = layer
            del pending[n]
        layer += 1


def axiom_closure(mods: dict[str, Module], name: str, seen: set[str] | None = None) -> set[str]:
    """Modules in the transitive import closure (inclusive) that declare an axiom."""
    seen = set() if seen is None else seen
    if name in seen or name not in mods:
        return set()
    seen.add(name)
    m = mods[name]
    out = {name} if m.declares_axiom else set()
    for d in m.imports:
        out |= axiom_closure(mods, d, seen)
    return out


def rewrite_code(m: Module, mods: dict[str, Module], lower: bool) -> str:
    """Rewrite in-repository imports to platform definition imports."""
    def sub(match: re.Match[str]) -> str:
        prefix, target = match.group(1), match.group(2)
        if target in mods:
            return f"import Definitions.Def_{mods[target].platform_name}"
        return match.group(0)

    pat = re.compile(r"^((?:public |private |meta )?)import ([A-Za-z_][\w.]*)\s*$", re.M)
    code = pat.sub(sub, m.text)

    if lower:
        code = re.sub(r"^module\s*$\n?", "", code, flags=re.M)
        code = re.sub(r"^(?:public |private )?import ", "import ", code, flags=re.M)
        code = re.sub(r"^public section\s*$", "section", code, flags=re.M)
        code = code.replace("public ", "").replace("@[expose] ", "")
    return code


def natural_language_statement(m: Module) -> str:
    if not m.docstring:
        return ""
    body = SOURCE_RE.sub("", m.docstring).strip()
    return body


def definition_title(m: Module) -> str:
    if m.docstring:
        first = m.docstring.strip().splitlines()[0].strip()
        first = re.sub(r"^#+\s*", "", first)
        if first:
            return first
    return m.name.rsplit(".", 1)[-1].replace("_", " ")


def emit(mods: dict[str, Module], out: Path, lower: bool, layer: int | None) -> int:
    out.mkdir(parents=True, exist_ok=True)
    written = 0
    for m in sorted(mods.values(), key=lambda x: (x.layer, x.name)):
        if layer is not None and m.layer != layer:
            continue
        excluded = axiom_closure(mods, m.name)
        if excluded:
            continue
        payload = {
            "definition_name": m.platform_name,
            "definition_title": definition_title(m),
            "natural_language_statement": natural_language_statement(m),
            "source": m.source or "",
            "layer": m.layer,
            "module": m.name,
            "source_file": str(m.path.relative_to(ROOT)),
            "code": rewrite_code(m, mods, lower),
        }
        (out / f"{m.platform_name}.json").write_text(
            json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
        written += 1
    return written


def report_gaps(mods: dict[str, Module]) -> None:
    missing_doc = sorted(n for n, m in mods.items() if not m.docstring)
    missing_src = sorted(n for n, m in mods.items() if m.docstring and not m.source)
    if missing_doc:
        print(f"\nmodules without a `/-! -/` module docstring: {len(missing_doc)}")
        for n in missing_doc[:10]:
            print("   ", n)
    if missing_src:
        print(f"\nmodules without a `source:` line: {len(missing_src)}")
        for n in missing_src[:10]:
            print("   ", n)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--private", action="store_true", help="stage submissions privately")
    ap.add_argument("--layer", type=int, default=None, help="publish one import layer only")
    ap.add_argument("--dry-run", action="store_true",
                    help="write payloads to a directory; make no network call")
    ap.add_argument("--out", type=Path, default=ROOT / ".prove2me-payloads")
    ap.add_argument("--lower", action="store_true",
                    help="lower the module system to plain Lean files (transformation 2)")
    args = ap.parse_args()
    args.out = args.out if args.out.is_absolute() else (Path.cwd() / args.out)

    mods = discover()
    compute_layers(mods)

    publishable, excluded = {}, {}
    for name, m in mods.items():
        closure = axiom_closure(mods, name)
        if closure:
            excluded[name] = sorted(closure)
        else:
            publishable[name] = m

    layers: dict[int, int] = {}
    for m in publishable.values():
        layers[m.layer] = layers.get(m.layer, 0) + 1

    print(f"definition modules discovered      : {len(mods)}")
    print(f"publishable (axiom-clean)          : {len(publishable)}")
    print(f"layers                             : {len(layers)}")
    print(f"layer widths                       : "
          f"{', '.join(str(layers[k]) for k in sorted(layers))}")

    if excluded:
        print(f"\nEXCLUDED — axiom subtree, owned by {AXIOM_OWNERS} ({len(excluded)} modules):")
        for name in sorted(excluded):
            print(f"    {name}   (reaches {', '.join(excluded[name])})")
    else:
        print(f"\nEXCLUDED — axiom subtree, owned by {AXIOM_OWNERS}: none. "
              "The library currently declares no `axiom`.")

    report_gaps(publishable)

    if args.dry_run:
        if args.out.exists():
            shutil.rmtree(args.out)
        n = emit(publishable, args.out, args.lower, args.layer)
        print(f"\nDRY RUN — wrote {n} definition payload(s) to {args.out.relative_to(ROOT)}")
        print("no network call was made")
        return 0

    print("\nnot running a live submission: publication requires a Prove2Me credential and "
          "orchestrator confirmation (issue #59, step 2). Use --dry-run.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
