#!/usr/bin/env python3
"""Generate the corpus website from the agent-memory vault's reference notes.

The notes are authored in an Obsidian-style vault: YAML frontmatter, wikilinks,
a title repeated as an H1 two to four times at the top of the body, and absolute
paths into a local Zotero store.  None of that belongs on a public site, and the
vault itself is private, so this script renders a self-contained Quarto tree that
CI can build without the vault present.

Run it after the vault changes; commit what it writes.

    python3 site/build.py [--vault DIR]
"""

from __future__ import annotations

import argparse
import re
import shutil
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

DEFAULT_VAULT = Path.home() / ".agent-memory-vault/projects/github.com__dzackgarza__lean-categories/references"
SITE = Path(__file__).resolve().parent

# Where each genre of note lands, and the sidebar section that holds it.
UNIT_ID = re.compile(r"\b(FC\d{2})-([A-Z]\d*|C\d+|[A-Z]{1,2})-U\d+\b")
ROUTE_ROW = re.compile(r"^\|\s*`FC\d{2}-[^`]+`\s*\|[^|]*\|\s*`([a-z-]+)`\s*\|")
FRONTMATTER = re.compile(r"\A---\n.*?\n---\n", re.DOTALL)
WIKILINK = re.compile(r"\[\[([^\]|]+)(?:\|([^\]]+))?\]\]")
BARE_LINK = re.compile(r"\[([^\]]+)\]\((?!https?:|#|\.)([a-z0-9][a-z0-9-]*)\)")
HOME_PATH = re.compile(r"/home/[a-z]+/(?:[\w.-]+/)*([\w.() -]+\.\w+)")

ROUTE_MEANING = {
    "mathlib": "Mathlib owns the unit outright.",
    "project-existing": "This repository already owns it.",
    "package-import": "A Lake-packaged library owns it.",
    "reference-port": "An external Lean development owns it and is ported with provenance.",
    "unmatched": "No checked Lean owner was found.",
}

SOURCE_TITLES = {
    "FC01": "FC01 — Dummit & Foote, *Abstract Algebra*",
    "FC02": "FC02 — Munkres, *Topology*",
    "FC03": "FC03 — Riehl, *Category Theory in Context*",
    "FC04": "FC04 — Atiyah & Macdonald, *Introduction to Commutative Algebra*",
    "FC05": "FC05 — Weibel, *An Introduction to Homological Algebra*",
    "FC06": "FC06 — Hartshorne, *Algebraic Geometry*",
    "FC07": "FC07 — Hatcher, *Algebraic Topology*",
    "FC08": "FC08 — Lee, *Introduction to Smooth Manifolds*",
    "FC09": "FC09 — Neukirch, *Algebraic Number Theory*",
    "FC10": "FC10 — Serre, *Local Fields*",
    "FC11": "FC11 — Peters & Sterk, *Symmetric and Quadratic Forms*",
    "FC12": "FC12 — Beauville, *Complex Algebraic Surfaces*",
    "FC13": "FC13 — Matsumura, *Commutative Ring Theory*",
    "FC14": "FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory*",
    "FC15": "FC15 — Humphreys, *Reflection Groups and Coxeter Groups*",
    "FC16": "FC16 — Humphreys, *Linear Algebraic Groups*",
}


@dataclass
class Page:
    """One rendered page: where it lands and what it is called."""

    path: str          # site-relative output path, without extension
    title: str
    body: str
    order: int = 0
    routes: Counter = field(default_factory=Counter)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def strip_frontmatter(text: str) -> str:
    return FRONTMATTER.sub("", text, count=1)


def collapse_repeated_headings(text: str) -> tuple[str, str]:
    """Drop the vault writer's duplicated leading headings; return (title, body).

    The notes open with the same title as an H1 two to four times, sometimes
    followed by an H2 saying it once more.  The first occurrence is the title.
    """
    lines = text.split("\n")
    title = ""
    seen: set[str] = set()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
        heading = re.match(r"^(#{1,3})\s+(.*\S)\s*$", line)
        if not heading:
            break
        # The same title recurs with and without its source code appended.
        key = re.sub(r"[^a-z0-9]+", "", re.sub(r"\s+FC\d{2}$", "", heading.group(2)).lower())
        if not title:
            title = heading.group(2)
            seen.add(key)
            i += 1
            continue
        if key in seen:
            i += 1
            continue
        break
    return title, "\n".join(lines[i:]).strip()


def sanitize(text: str, links: dict[str, str], titles: dict[str, str] | None = None) -> str:
    """Resolve vault links against the generated pages and remove local paths."""
    titles = titles or {}

    def wiki(match: re.Match[str]) -> str:
        target, label = match.group(1), match.group(2)
        slug = target.split("/")[-1].split("#")[0].strip()
        label = label or titles.get(slug) or slug.replace("-", " ")
        dest = links.get(slug)
        return f"[{label}]({dest})" if dest else label

    def bare(match: re.Match[str]) -> str:
        label, slug = match.group(1), match.group(2)
        dest = links.get(slug)
        return f"[{label}]({dest})" if dest else label

    text = WIKILINK.sub(wiki, text)
    text = BARE_LINK.sub(bare, text)
    text = HOME_PATH.sub(r"`\1`", text)
    return text


def source_of(text: str) -> tuple[str, str] | None:
    """The (source, chapter) block a coverage note certifies, from its unit IDs."""
    match = UNIT_ID.search(text)
    return (match.group(1), match.group(2)) if match else None


def contract_key(stem: str) -> tuple[str, str]:
    """FC04's chapter contracts are named without their source prefix."""
    rest = stem.removeprefix("provenance-contract-for-")
    parts = rest.split("-")
    if parts[0].startswith("fc"):
        return parts[0].upper(), "-".join(parts[1:]).upper()
    return "FC04", rest.upper()


def chapter_sort_key(chapter: str) -> tuple[int, str]:
    """Numbered chapters first, in order; lettered appendices after them."""
    if chapter.startswith("C") and chapter[1:].isdigit():
        return (int(chapter[1:]), "")
    return (10**6, chapter)


def colour_routes(body: str) -> str:
    """Tag the route cell so a page's shape is visible before it is read."""

    def tag(match: re.Match[str]) -> str:
        route = match.group(1)
        return f"[`{route}`]{{.route-{route}}}"

    return re.sub(
        r"(?<=\|)\s*`(mathlib|project-existing|package-import|reference-port|unmatched)`\s*(?=\|)",
        lambda m: f" {tag(m)} ",
        body,
    )


def wrap_wide_tables(body: str, columns: int = 5) -> str:
    """Put a scrolling box around any table too wide for the text measure."""
    out: list[str] = []
    block: list[str] = []

    def flush() -> None:
        if not block:
            return
        wide = block[0].count("|") > columns
        out.extend([":::: {.table-scroll}", "", *block, "", "::::"] if wide else block)
        block.clear()

    for line in body.split("\n"):
        if line.startswith("|"):
            block.append(line)
            continue
        flush()
        out.append(line)
    flush()
    return "\n".join(out)


def route_table(routes: Counter) -> str:
    total = sum(routes.values())
    if not total:
        return ""
    rows = ["| Route | Units | Share | Meaning |", "| --- | ---: | ---: | --- |"]
    for route, count in sorted(routes.items(), key=lambda kv: -kv[1]):
        share = f"{100 * count / total:.0f}%"
        rows.append(f"| `{route}` | {count} | {share} | {ROUTE_MEANING.get(route, '')} |")
    rows.append(f"| **total** | **{total}** | | |")
    return "\n".join(rows)


def build(vault: Path) -> list[Page]:
    notes = {p.stem: p for p in sorted(vault.glob("*.md")) if p.stem != "index"}
    pages: list[Page] = []
    links: dict[str, str] = {}

    coverage: dict[tuple[str, str], Path] = {}
    contracts: dict[tuple[str, str], Path] = {}
    per_source: dict[str, dict[str, Path]] = {}
    catalogues: dict[str, Path] = {}
    other: dict[str, Path] = {}

    for stem, path in notes.items():
        if stem.startswith("provenance-contract-for-"):
            contracts[contract_key(stem)] = path
        elif stem.startswith(("chapter-", "appendix-")):
            key = source_of(read(path))
            if key:
                coverage[key] = path
        elif stem.startswith(("foundational-corpus-units-", "foundational-corpus-mapping-")):
            code = re.search(r"-(fc\d{2})-", stem)
            if code:
                kind = "units" if "units" in stem else "mapping"
                per_source.setdefault(code.group(1).upper(), {})[kind] = path
        elif "definition-catalogue" in stem:
            catalogues[stem] = path
        else:
            other[stem] = path

    # Reserve every destination before rendering, so links resolve in one pass.
    for (src, chap) in coverage:
        links[coverage[(src, chap)].stem] = f"/sources/{src.lower()}/{chap.lower()}.html"
    for (src, chap), path in contracts.items():
        links[path.stem] = f"/sources/{src.lower()}/{chap.lower()}.html"
    for src, kinds in per_source.items():
        for kind, path in kinds.items():
            links[path.stem] = f"/sources/{src.lower()}/{kind}.html"
    for stem in catalogues:
        links[stem] = f"/catalogues/{stem}.html"
    for stem in other:
        links[stem] = f"/notes/{stem}.html"
    links["foundational-source-corpus"] = "/corpus.html"
    links["foundational-corpus-status"] = "/status.html"

    # A wikilink written without a label gets the destination page's own title.
    titles: dict[str, str] = {}
    for stem in links:
        path = notes.get(stem)
        if path:
            titles[stem] = re.sub(
                r"\s+FC\d{2}$", "", collapse_repeated_headings(strip_frontmatter(read(path)))[0]
            )

    def render(path: Path, out: str, fallback_title: str = "") -> Page:
        title, body = collapse_repeated_headings(strip_frontmatter(read(path)))
        # Chapter titles repeat their source code; the page already sits under it.
        title = re.sub(r"\s+FC\d{2}$", "", title or fallback_title)
        return Page(out, title, sanitize(body, links, titles))

    # Coverage pages, each carrying the provenance record of its own sweep.
    for (src, chap), path in sorted(coverage.items()):
        page = render(path, f"sources/{src.lower()}/{chap.lower()}")
        page.routes = Counter(m.group(1) for line in page.body.split("\n") if (m := ROUTE_ROW.match(line)))
        contract = contracts.get((src, chap))
        header = [
            f"{SOURCE_TITLES.get(src, src)} — block `{src}-{chap}`.",
            "",
            route_table(page.routes),
            "",
        ]
        if contract:
            _, record = collapse_repeated_headings(strip_frontmatter(read(contract)))
            record = sanitize(record, links, titles)
            record = re.sub(r"^#+\s+Provenance contract.*$", "", record, flags=re.MULTILINE).strip()
            header += [
                "::: {.callout-note collapse=\"true\"}",
                "## Provenance of this sweep",
                "",
                record,
                ":::",
                "",
                "",
            ]
        page.body = "\n".join(header) + wrap_wide_tables(colour_routes(page.body))
        page.order = chapter_sort_key(chap)[0]
        pages.append(page)

    for src, kinds in sorted(per_source.items()):
        for kind, path in sorted(kinds.items()):
            pages.append(render(path, f"sources/{src.lower()}/{kind}"))
    for stem, path in sorted(catalogues.items()):
        pages.append(render(path, f"catalogues/{stem}"))
    for stem, path in sorted(other.items()):
        pages.append(render(path, f"notes/{stem}"))

    pages.append(render(vault / "foundational-source-corpus.md", "corpus"))
    pages.append(render(vault / "foundational-corpus-status.md", "status"))
    return pages


def write_pages(pages: list[Page]) -> None:
    for page in pages:
        out = SITE / f"{page.path}.md"
        out.parent.mkdir(parents=True, exist_ok=True)
        title = page.title.replace('"', "'")
        out.write_text(f'---\ntitle: "{title}"\n---\n\n{page.body}\n', encoding="utf-8")


def write_source_indexes(pages: list[Page]) -> dict[str, Counter]:
    """One landing page per source, listing its blocks and their coverage."""
    by_source: dict[str, list[Page]] = {}
    for page in pages:
        parts = page.path.split("/")
        if parts[0] == "sources":
            by_source.setdefault(parts[1].upper(), []).append(page)

    totals: dict[str, Counter] = {}
    for src, group in sorted(by_source.items()):
        routes = Counter()
        for page in group:
            routes.update(page.routes)
        totals[src] = routes

        lines: list[str] = []
        support = [p for p in group if p.path.endswith(("/units", "/mapping"))]
        blocks = sorted(
            (p for p in group if p not in support),
            key=lambda p: chapter_sort_key(p.path.split("/")[-1].upper()),
        )
        if support:
            lines += ["## The source, enumerated", ""]
            for page in support:
                kind = page.path.split("/")[-1]
                what = "Every definition, theorem and example, assigned a unit ID." if kind == "units" else "Where each unit is expected to land."
                lines.append(f"- [{page.title}]({kind}.html) — {what}")
            lines.append("")
        if blocks:
            lines += ["## Coverage by block", "", "| Block | Units | Mathlib | Owned here | Ported | Unmatched |", "| --- | ---: | ---: | ---: | ---: | ---: |"]
            for page in blocks:
                r = page.routes
                name = page.path.split("/")[-1]
                lines.append(
                    f"| [{page.title}]({name}.html) | {sum(r.values())} | {r['mathlib']} | "
                    f"{r['project-existing']} | {r['reference-port'] + r['package-import']} | {r['unmatched']} |"
                )
            lines += ["", "### This source in total", "", route_table(routes)]
        else:
            lines += [
                "This source is in the corpus and has not been swept against Lean yet.",
                "Its units are enumerated above; no unit has been routed.",
            ]

        out = SITE / "sources" / src.lower() / "index.md"
        heading = SOURCE_TITLES.get(src, src).replace("*", "").replace('"', "'")
        out.write_text(f'---\ntitle: "{heading}"\n---\n\n' + "\n".join(lines) + "\n", encoding="utf-8")
    return totals


def write_coverage(totals: dict[str, Counter]) -> Counter:
    grand = Counter()
    for routes in totals.values():
        grand.update(routes)

    lines = [
        "The corpus is a fixed list of graduate textbooks, read cover to cover. Every",
        "definition, theorem, lemma, example and remark in a swept chapter becomes a",
        "numbered *unit*, and every unit is assigned exactly one route: a Lean declaration",
        "that owns it, or a finding that nothing does.",
        "",
        "Routes are strict about bundles. A unit is credited only when a checked declaration",
        "carries the whole statement the source makes, hypotheses included. A partial match",
        "is recorded as unmatched, with the partial named in its row.",
        "",
        "## Every source",
        "",
        "| Source | Units | Mathlib | Owned here | Ported | Unmatched |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for src, r in sorted(totals.items()):
        total = sum(r.values())
        if not total:
            continue
        lines.append(
            f"| [{SOURCE_TITLES.get(src, src)}](sources/{src.lower()}/) | {total} | {r['mathlib']} | "
            f"{r['project-existing']} | {r['reference-port'] + r['package-import']} | {r['unmatched']} |"
        )
    lines += ["", "## In total", "", route_table(grand)]
    (SITE / "coverage.md").write_text(
        '---\ntitle: "Coverage"\n---\n\n' + "\n".join(lines) + "\n", encoding="utf-8"
    )
    return grand


def write_index(grand: Counter, swept: int, sources: int) -> None:
    total = sum(grand.values())
    body = f"""
This site publishes a unit-by-unit survey of what standard graduate mathematics
textbooks state, and which Lean declaration — if any — already owns each
statement. The corpus fixes {sources} books; {swept} of them have been swept so far.

It exists because `lean-categories` authors as little Lean as possible. Before
anything is written here, the reuse gate asks whether Mathlib, a packaged
library, or an external development already proves it. The survey is the
accumulated answer, and its unmatched rows are the roadmap.

## What is in it

| | |
| --- | ---: |
| Source units read and routed | **{total:,}** |
| Owned by Mathlib | {grand['mathlib']:,} |
| Owned by an external Lean development | {grand['reference-port'] + grand['package-import']:,} |
| Owned by this repository | {grand['project-existing']:,} |
| **No Lean owner found** | **{grand['unmatched']:,}** |

Every row names the declarations it compared against, at a pinned Mathlib
commit, and says in prose how the interfaces differ. Unmatched rows name the
partial machinery that exists and the gap that stops it closing the statement,
so each one reads as a concrete formalization target.

## Where to start

- [Coverage](coverage.qmd) — the table above, broken out by source and chapter.
- [The corpus](corpus.qmd) — which books, which editions, what scope, and the
  prerequisite order they are read in.
- [Sweep status](status.qmd) — how far each source has been taken.
- [Definition catalogues](catalogues/) — every definition in a source, with its
  page reference.

## How to read a row

The route says who owns the unit:

{route_table(grand)}

## Caveats

The survey is a search, not a proof. An unmatched row asserts that a documented
search found no owner on the pinned revisions it names — not that none exists.
Mathlib moves; a row is only as current as the commits in its provenance note.
Where a claim here and the Lean disagree, the Lean is right.
"""
    (SITE / "index.md").write_text(
        '---\ntitle: "The foundational corpus"\n---\n' + body, encoding="utf-8"
    )


def write_quarto(totals: dict[str, Counter]) -> None:
    lines = [
        "project:",
        "  type: website",
        "  output-dir: _site",
        "",
        "website:",
        '  title: "lean-categories · corpus"',
        '  description: "A unit-by-unit survey of graduate mathematics against Mathlib."',
        "  site-url: https://dzackgarza.github.io/lean-categories/",
        "  repo-url: https://github.com/dzackgarza/lean-categories",
        "  search:",
        "    location: sidebar",
        "    type: overlay",
        "  navbar:",
        "    left:",
        '      - text: "Coverage"',
        "        href: coverage.md",
        '      - text: "The corpus"',
        "        href: corpus.md",
        '      - text: "Catalogues"',
        "        href: catalogues/index.md",
        "    right:",
        "      - icon: github",
        "        href: https://github.com/dzackgarza/lean-categories",
        "  sidebar:",
        "    style: docked",
        "    collapse-level: 1",
        "    contents:",
        "      - index.md",
        "      - coverage.md",
        "      - corpus.md",
        "      - status.md",
        '      - section: "Sources"',
        "        contents:",
    ]
    for src in sorted(totals):
        directory = SITE / "sources" / src.lower()
        lines += [
            f'          - section: "{src}"',
            f"            href: sources/{src.lower()}/index.md",
            "            contents:",
        ]
        for name in ("units", "mapping"):
            if (directory / f"{name}.md").exists():
                lines.append(f"              - sources/{src.lower()}/{name}.md")
        blocks = sorted(
            (p.stem for p in directory.glob("*.md") if p.stem not in {"index", "units", "mapping"}),
            key=lambda s: chapter_sort_key(s.upper()),
        )
        for block in blocks:
            lines.append(f"              - sources/{src.lower()}/{block}.md")

    lines += [
        '      - section: "Definition catalogues"',
        "        href: catalogues/index.md",
        "        contents:",
        "          - catalogues/*.md",
        '      - section: "Notes and audits"',
        "        href: notes/index.md",
        "        contents:",
        "          - notes/*.md",
        "  page-footer:",
        '    left: "Generated from the project\'s reference notes by `site/build.py`."',
        '    right: "The Lean is the authority; where this site differs, the Lean is right."',
        "",
        "format:",
        "  html:",
        "    theme:",
        "      light: cosmo",
        "      dark: darkly",
        "    toc: true",
        "    toc-depth: 2",
        # A coverage table is six columns, two of them paragraphs: it needs the window.
        "    page-layout: full",
        "    grid:",
        "      sidebar-width: 300px",
        "      margin-width: 0px",
        "    css: styles.css",
        "    link-external-newwindow: true",
        "",
    ]
    (SITE / "_quarto.yml").write_text("\n".join(lines), encoding="utf-8")


def write_section_indexes(pages: list[Page]) -> None:
    catalogues = sorted((p for p in pages if p.path.startswith("catalogues/")), key=lambda p: p.title)
    body = [
        "A catalogue lists every definition a source states, in the order the source",
        "states it, with the section and page it appears on. The catalogues are the",
        "denominator the coverage sweeps are measured against.",
        "",
    ]
    for page in catalogues:
        body.append(f"- [{page.title}]({page.path.split('/')[-1]}.html)")
    (SITE / "catalogues" / "index.md").write_text(
        '---\ntitle: "Definition catalogues"\n---\n\n' + "\n".join(body) + "\n", encoding="utf-8"
    )

    notes = sorted((p for p in pages if p.path.startswith("notes/")), key=lambda p: p.title)
    body = [
        "Working records: source surveys, resolved ambiguities, and audits of this",
        "repository taken at a named commit. An audit describes the tree as it stood on",
        "its own date and is not maintained afterwards.",
        "",
    ]
    for page in notes:
        body.append(f"- [{page.title}]({page.path.split('/')[-1]}.html)")
    (SITE / "notes" / "index.md").write_text(
        '---\ntitle: "Notes and audits"\n---\n\n' + "\n".join(body) + "\n", encoding="utf-8"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vault", type=Path, default=DEFAULT_VAULT)
    args = parser.parse_args()

    assert args.vault.is_dir(), f"vault reference directory not found: {args.vault}"

    for stale in ("sources", "catalogues", "notes"):
        shutil.rmtree(SITE / stale, ignore_errors=True)

    pages = build(args.vault)
    write_pages(pages)
    write_section_indexes(pages)
    totals = write_source_indexes(pages)
    grand = write_coverage(totals)
    write_index(grand, len([s for s, r in totals.items() if sum(r.values())]), len(totals))
    write_quarto(totals)
    print(f"{len(pages)} pages, {sum(grand.values())} units across {len(totals)} sources")


if __name__ == "__main__":
    main()
