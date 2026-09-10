#!/usr/bin/env python3
"""Generate the corpus website from the agent-memory vault's reference notes.

The corpus is a fixed list of graduate textbooks read cover to cover. Every
definition, theorem, lemma, example and remark in a read chapter is a numbered
*unit* carrying its statement and its location in the book; a swept chapter
additionally routes each unit to the Lean declaration that owns it, or records
that nothing does.

Those two facts live in separate vault notes — the enumeration in one, the Lean
sweep in another — and neither is much use alone. This script joins them on the
unit ID and renders one page per chapter, where a unit is a mathematical
statement that happens to carry a Lean verdict, rather than a row of audit
bookkeeping. It also resolves every declaration name, source path, commit and
pull request into a link, because a survey of what Lean owns is worth little if
the name of the owner is not one click from the thing it names.

The vault is private and its notes carry Obsidian frontmatter, wikilinks,
repeated headings, unclosed code fences and absolute Zotero paths; none of that
survives into the site, and what this writes is committed so CI can build from
the checkout alone.

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

FRONTMATTER = re.compile(r"\A---\n.*?\n---\n", re.DOTALL)
VAULT_FENCE = re.compile(r"^\s*`{3,}\s*markdown\s+#projects/\S+\s*$")
WIKILINK = re.compile(r"\[\[([^\]|]+)(?:\|([^\]]+))?\]\]")
BARE_LINK = re.compile(r"\[([^\]]+)\]\((?!https?:|#|\.)([a-z0-9][a-z0-9-]*)\)")
HOME_PATH = re.compile(r"/home/[a-z]+/(?:[\w.-]+/)*([\w.() -]+\.\w+)")
UNIT_ID = re.compile(r"\b(FC\d{2})-([A-Z]\d*|C\d+|[A-Z]{1,2})-U(\d+)\b")
TABLE_ROW = re.compile(r"^\|(.*)\|\s*$")

MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs"
MATHLIB_REPO = "https://github.com/leanprover-community/mathlib4"
THIS_REPO = "https://github.com/dzackgarza/lean-categories"

CODE_SPAN = re.compile(r"`([^`\n]+)`")
LEAN_IDENT = re.compile(r"\A[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)+\Z")
COMMIT = re.compile(r"\A[0-9a-f]{40}\Z")
EXTERNAL = re.compile(r"\A(?P<repo>[\w.-]+/[\w.-]+)@(?P<sha>[0-9a-f]{7,40})(?:::|/)(?P<path>[^:]+\.lean)")
PULL_REQUEST = re.compile(r"(?<![\w/#])#(\d{4,6})\b")

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
class Unit:
    """One statement of the source text, as the enumeration records it."""

    uid: str
    source: str
    block: str
    kind: str = ""
    location: str = ""
    statement: str = ""
    depends: list[str] = field(default_factory=list)


@dataclass
class Route:
    """What the Lean sweep found for one unit."""

    verdict: str = ""
    route: str = ""
    targets: str = ""
    provenance: str = ""
    comparison: str = ""


@dataclass
class Block:
    """A chapter or appendix: the page unit of this site."""

    source: str
    name: str
    title: str
    units: list[Unit] = field(default_factory=list)
    routes: dict[str, Route] = field(default_factory=dict)
    provenance: str = ""

    @property
    def counts(self) -> Counter:
        return Counter(r.route for r in self.routes.values() if r.route)

    @property
    def href(self) -> str:
        return f"sources/{self.source.lower()}/{self.name.lower()}"


@dataclass
class Page:
    path: str
    title: str
    body: str


# --- reading the vault -------------------------------------------------------


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def strip_vault_fences(text: str) -> str:
    """Remove the wrapper the vault writer left around some notes.

    Those notes open with a code fence naming the note's own vault path, and the
    fence is never closed, so every heading and table after it renders as
    literal text. The fences are packaging, not content.
    """
    lines = [line for line in text.split("\n") if not VAULT_FENCE.match(line)]
    if sum(1 for line in lines if line.strip().startswith("```")) % 2:
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip() == "```":
                del lines[i]
                break
    return "\n".join(lines)


def clean(text: str) -> str:
    return strip_vault_fences(FRONTMATTER.sub("", text, count=1))


def collapse_repeated_headings(text: str) -> tuple[str, str]:
    """Drop the writer's duplicated leading headings; return (title, body).

    A note opens with its own title as an H1 two to four times, sometimes with
    the source code appended to some of them and not others.
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
        heading = re.match(r"^#{1,3}\s+(.*\S)\s*$", line)
        if not heading:
            break
        key = re.sub(r"[^a-z0-9]+", "", re.sub(r"\s+FC\d{2}$", "", heading.group(1)).lower())
        if not title:
            title, i = heading.group(1), i + 1
            seen.add(key)
            continue
        if key in seen:
            i += 1
            continue
        break
    body = "\n".join(lines[i:]).strip()

    # A body whose first heading is a lone H1 is titled by it, and repeating it
    # under the page title just says the same thing twice.
    rest = body.split("\n")
    first = next((n for n, line in enumerate(rest) if line.strip()), None)
    if first is not None and rest[first].startswith("# "):
        if sum(1 for line in rest if line.startswith("# ")) == 1:
            body = "\n".join(rest[first + 1 :]).strip()
    return re.sub(r"\s+FC\d{2}$", "", title), body


def table_cells(line: str) -> list[str]:
    row = TABLE_ROW.match(line)
    return [c.strip() for c in row.group(1).split("|")] if row else []


def column_map(header: list[str]) -> dict[str, int]:
    """Match the enumeration's columns by name; sources order them differently."""
    columns: dict[str, int] = {}
    for i, name in enumerate(header):
        lowered = name.lower()
        if lowered == "id":
            columns["uid"] = i
        elif "epend" in lowered:
            columns["depends"] = i
        elif "kind" in lowered:
            columns["kind"] = i
        elif lowered in {"location", "source"}:
            columns["location"] = i
        else:
            columns.setdefault("statement", i)
    return columns


def parse_units(text: str) -> tuple[str, dict[tuple[str, str], tuple[str, list[Unit]]]]:
    """Read an enumeration note into (preamble, {(source, block): (title, units)})."""
    intro: list[str] = []
    blocks: dict[tuple[str, str], tuple[str, list[Unit]]] = {}
    heading = ""
    columns: dict[str, int] = {}
    seen_unit = False

    for line in text.split("\n"):
        if line.startswith("#"):
            heading = line.lstrip("#").strip()
            columns = {}
            continue
        cells = table_cells(line)
        if not cells:
            if not seen_unit:
                intro.append(line)
            continue
        if not columns:
            if cells and cells[0].lower() == "id":
                columns = column_map(cells)
            continue
        if set("".join(cells)) <= set("-: "):
            continue
        found = UNIT_ID.search(cells[columns.get("uid", 0)])
        if not found:
            continue
        seen_unit = True
        source, block = found.group(1), found.group(2)

        def cell(name: str) -> str:
            index = columns.get(name)
            return cells[index] if index is not None and index < len(cells) else ""

        unit = Unit(
            uid=found.group(0),
            source=source,
            block=block,
            kind=cell("kind").strip("`"),
            location=cell("location"),
            statement=cell("statement"),
            depends=[m.group(0) for m in UNIT_ID.finditer(cell("depends"))],
        )
        title, units = blocks.setdefault((source, block), (heading, []))
        units.append(unit)
        if not title:
            blocks[(source, block)] = (heading, units)
    return "\n".join(intro).strip(), blocks


def parse_coverage(text: str) -> tuple[str, dict[str, Route]]:
    """Read a sweep note into (block title, {unit ID: route})."""
    routes: dict[str, Route] = {}
    for line in text.split("\n"):
        cells = table_cells(line)
        if len(cells) < 3:
            continue
        found = UNIT_ID.search(cells[0])
        if not found or not cells[0].startswith("`"):
            continue
        routes[found.group(0)] = Route(
            verdict=cells[1],
            route=cells[2].strip("` "),
            targets=cells[3] if len(cells) > 3 else "",
            provenance=cells[4] if len(cells) > 4 else "",
            comparison=cells[5] if len(cells) > 5 else "",
        )
    return "", routes


# --- turning vault prose into web prose --------------------------------------


def sanitize(text: str, links: dict[str, str], titles: dict[str, str]) -> str:
    """Resolve the vault's own links and strip absolute local paths."""

    def wiki(match: re.Match[str]) -> str:
        slug = match.group(1).split("/")[-1].split("#")[0].strip()
        label = match.group(2) or titles.get(slug) or slug.replace("-", " ")
        dest = links.get(slug)
        return f"[{label}]({dest})" if dest else label

    def bare(match: re.Match[str]) -> str:
        dest = links.get(match.group(2))
        return f"[{match.group(1)}]({dest})" if dest else match.group(1)

    text = WIKILINK.sub(wiki, text)
    text = BARE_LINK.sub(bare, text)
    return HOME_PATH.sub(r"`\1`", text)


def docs_url(path: str, decl: str = "") -> str:
    page = f"{MATHLIB_DOCS}/{path[: -len('.lean')]}.html"
    return f"{page}#{decl}" if decl else page


def target_url(text: str) -> str:
    """Where a code span points, if anywhere."""
    if external := EXTERNAL.match(text):
        return f"https://github.com/{external['repo']}/blob/{external['sha']}/{external['path']}"

    path, sep, decls = text.partition("::")
    if sep and path.endswith(".lean"):
        named = [d.strip() for d in re.split(r"[,;]", decls) if LEAN_IDENT.match(d.strip())]
        decl = named[0] if len(named) == 1 else ""
        if path.startswith("Mathlib/"):
            return docs_url(path, decl)
        if path.startswith(("LeanCategories/", "LeanCategoriesSpherePacking/")):
            return f"{THIS_REPO}/blob/main/{path}"
        return ""

    if text.endswith(".lean"):
        if text.startswith("Mathlib/"):
            return docs_url(text)
        if text.startswith(("LeanCategories/", "LeanCategoriesSpherePacking/")):
            return f"{THIS_REPO}/blob/main/{text}"
    if COMMIT.match(text):
        return f"{MATHLIB_REPO}/commit/{text}"
    if LEAN_IDENT.match(text):
        # A bare declaration name: the docs' own search resolves it.
        return f"{MATHLIB_DOCS}/find/?pattern={text}#doc"
    return ""


def linkify(body: str) -> str:
    """Point every declaration, source path, commit and pull request at its source."""

    def span(match: re.Match[str]) -> str:
        url = target_url(match.group(1))
        return f"[`{match.group(1)}`]({url})" if url else match.group(0)

    out: list[str] = []
    for chunk in re.split(r"(\[[^\]]*\]\([^)]*\))", body):
        if chunk.startswith("["):
            out.append(chunk)  # already a link
            continue
        out.append(PULL_REQUEST.sub(rf"[#\1]({MATHLIB_REPO}/pull/\1)", CODE_SPAN.sub(span, chunk)))
    return "".join(out)


def unit_href(uid: str, here: tuple[str, str], known: set[tuple[str, str]]) -> str:
    """A link to another unit's entry, which may be on another page."""
    found = UNIT_ID.match(uid)
    if not found:
        return uid
    source, block = found.group(1), found.group(2)
    anchor = uid.lower()
    if (source, block) not in known:
        return f"`{uid}`"
    if (source, block) == here:
        return f"[`{uid}`](#{anchor})"
    if source == here[0]:
        return f"[`{uid}`]({block.lower()}.html#{anchor})"
    return f"[`{uid}`](../{source.lower()}/{block.lower()}.html#{anchor})"


def route_badge(route: str) -> str:
    return f"[`{route}`]{{.route-{route}}}" if route else ""


def route_table(routes: Counter) -> str:
    total = sum(routes.values())
    if not total:
        return ""
    rows = ["| Route | Units | Share | Meaning |", "| --- | ---: | ---: | --- |"]
    for route, count in sorted(routes.items(), key=lambda kv: -kv[1]):
        rows.append(f"| {route_badge(route)} | {count} | {100 * count / total:.0f}% | {ROUTE_MEANING.get(route, '')} |")
    rows.append(f"| **total** | **{total}** | | |")
    return "\n".join(rows)


# --- rendering ---------------------------------------------------------------


BARE_KIND = re.compile(r"\A(definition|theorem|lemma|proposition|corollary|example|remark|notation|convention|construction|axiom|exercise)s?\Z", re.I)


def unit_heading(unit: Unit, route: Route | None) -> str:
    """Name the unit.

    Most sources record a kind and a short name together ("Theorem: Theorem 28.1
    (transitivity)"). A few record only the bare kind, which would give a page a
    hundred headings all reading "Definition", so those take their name from the
    opening clause of the statement instead.
    """
    kind = unit.kind or (route.verdict if route else "") or "Unit"
    if not BARE_KIND.match(kind.strip()):
        return kind
    opening = re.split(r"(?<=[a-z0-9)])[:.;] ", re.sub(r"\s+", " ", unit.statement), maxsplit=1)[0]
    opening = re.sub(r"[*_`]", "", opening).strip()
    if not opening:
        return kind
    if len(opening) > 80:
        opening = opening[:77].rsplit(" ", 1)[0] + "…"
    return f"{kind}: {opening}"


def render_unit(
    unit: Unit,
    route: Route | None,
    here: tuple[str, str],
    known: set[tuple[str, str]],
    usual_provenance: str = "",
) -> str:
    anchor = unit.uid.lower()
    lines = [f"### {unit_heading(unit, route)} {{#{anchor}}}", ""]

    meta = [f"`{unit.uid}`"]
    if unit.location:
        meta.append(unit.location)
    if unit.depends:
        meta.append("after " + ", ".join(unit_href(d, here, known) for d in unit.depends))
    if route and route.route:
        meta.append(route_badge(route.route))
    lines += ["::: {.unit-meta}", " · ".join(meta), ":::", ""]

    if unit.statement:
        lines += [unit.statement, ""]

    if route and (route.targets or route.comparison):
        owner = "In Lean" if route.route != "unmatched" else "Not in Lean"
        detail = []
        if route.targets and route.targets != "—":
            detail.append(route.targets)
        if route.comparison:
            detail.append(route.comparison)
        lines += ["::: {.unit-lean}", f"**{owner}.** " + " — ".join(detail), ":::", ""]
        # The revisions searched are the chapter's, stated once in its note; only
        # a unit searched differently says so here.
        if route.provenance and route.provenance != usual_provenance:
            lines += [f"[Searched: {route.provenance}]{{.unit-provenance}}", ""]
    return "\n".join(lines)


def render_block(block: Block, known: set[tuple[str, str]]) -> Page:
    here = (block.source, block.name)
    counts = block.counts
    lead = [f"{SOURCE_TITLES.get(block.source, block.source)} — block `{block.source}-{block.name}`.", ""]

    if counts:
        total = sum(counts.values())
        owned = total - counts["unmatched"]
        lead += [
            f"{len(block.units) or total} units. "
            f"{owned} have a Lean owner; {counts['unmatched']} do not.",
            "",
            route_table(counts),
            "",
        ]
    else:
        lead += [
            "This chapter is enumerated but not yet swept against Lean: the statements",
            "below carry no routing verdict.",
            "",
        ]

    if block.provenance:
        lead += ['::: {.callout-note collapse="true"}', "## How this chapter was searched", "", block.provenance, ":::", ""]

    usual = Counter(r.provenance for r in block.routes.values() if r.provenance)
    usual_provenance = usual.most_common(1)[0][0] if usual else ""

    body = [*lead]
    unrouted = dict(block.routes)
    for unit in block.units:
        body.append(render_unit(unit, block.routes.get(unit.uid), here, known, usual_provenance))
        unrouted.pop(unit.uid, None)
    # A routed unit the enumeration does not list still belongs on the page.
    for uid, route in unrouted.items():
        found = UNIT_ID.match(uid)
        body.append(
            render_unit(
                Unit(uid=uid, source=found.group(1), block=found.group(2), kind=route.verdict),
                route,
                here,
                known,
                usual_provenance,
            )
        )
    return Page(block.href, block.title, "\n".join(body))


def render_source_index(source: str, blocks: list[Block], intro: str, extra: list[Page]) -> Page:
    counts = Counter()
    for block in blocks:
        counts.update(block.counts)
    units = sum(len(b.units) or sum(b.counts.values()) for b in blocks)

    lines = []
    if intro:
        lines += [intro, ""]
    lines += [f"**{units} source units** across {len(blocks)} chapters and appendices.", ""]

    lines += ["| Chapter | Units | In Lean | Not in Lean | Swept |", "| --- | ---: | ---: | ---: | :-: |"]
    for block in blocks:
        c = block.counts
        routed = sum(c.values())
        n = len(block.units) or routed
        owned = routed - c["unmatched"] if routed else 0
        lines.append(
            f"| [{block.title}]({block.name.lower()}.html) | {n} | "
            f"{owned if routed else '—'} | {c['unmatched'] if routed else '—'} | "
            f"{'yes' if routed else 'no'} |"
        )
    if counts:
        lines += ["", "### Routes across this source", "", route_table(counts)]
    for page in extra:
        lines += ["", f"- [{page.title}]({page.path.split('/')[-1]}.html)"]
    return Page(f"sources/{source.lower()}/index", SOURCE_TITLES.get(source, source), "\n".join(lines))


def write(page: Page) -> None:
    out = SITE / f"{page.path}.md"
    out.parent.mkdir(parents=True, exist_ok=True)
    title = re.sub(r"[*`]", "", page.title).replace('"', "'")
    out.write_text(f'---\ntitle: "{title}"\n---\n\n{page.body}\n', encoding="utf-8")


# --- assembling the site -----------------------------------------------------


def build(vault: Path) -> tuple[dict[str, list[Block]], list[Page]]:
    notes = {p.stem: p for p in sorted(vault.glob("*.md")) if p.stem != "index"}

    units_notes: dict[str, Path] = {}
    mapping_notes: dict[str, Path] = {}
    coverage_notes: list[Path] = []
    contracts: dict[tuple[str, str], Path] = {}
    catalogues: dict[str, Path] = {}
    other: dict[str, Path] = {}

    for stem, path in notes.items():
        code = re.search(r"-(fc\d{2})[-.]", stem)
        if stem.startswith("provenance-contract-for-"):
            rest = stem.removeprefix("provenance-contract-for-").split("-")
            key = (rest[0].upper(), "-".join(rest[1:]).upper()) if rest[0].startswith("fc") else ("FC04", "-".join(rest).upper())
            contracts[key] = path
        elif stem.startswith("foundational-corpus-units-") and code:
            units_notes[code.group(1).upper()] = path
        elif stem.startswith("foundational-corpus-mapping-") and code:
            mapping_notes[code.group(1).upper()] = path
        elif stem.startswith(("chapter-", "appendix-")):
            coverage_notes.append(path)
        elif "definition-catalogue" in stem:
            catalogues[stem] = path
        elif stem not in {"foundational-source-corpus", "foundational-corpus-status"}:
            other[stem] = path

    # Every destination is reserved before any page is rendered, so that the
    # vault's own cross-references resolve in a single pass.
    links: dict[str, str] = {
        "foundational-source-corpus": "/corpus.html",
        "foundational-corpus-status": "/status.html",
    }
    for source, path in units_notes.items():
        links[path.stem] = f"/sources/{source.lower()}/"
    for source, path in mapping_notes.items():
        links[path.stem] = f"/sources/{source.lower()}/mapping.html"
    for stem in catalogues:
        links[stem] = f"/catalogues/{stem}.html"
    for stem in other:
        links[stem] = f"/notes/{stem}.html"
    titles = {
        stem: collapse_repeated_headings(clean(read(notes[stem])))[0]
        for stem in links
        if stem in notes
    }

    def prose(text: str) -> str:
        return linkify(sanitize(text, links, titles))

    # The enumeration is the spine: it holds the mathematics.
    blocks: dict[tuple[str, str], Block] = {}
    intros: dict[str, str] = {}
    for source, path in units_notes.items():
        intro, parsed = parse_units(clean(read(path)))
        intros[source] = prose(intro)
        for (src, name), (title, units) in parsed.items():
            blocks[(src, name)] = Block(src, name, title or f"{name}", units)

    # The sweeps annotate it.
    for path in coverage_notes:
        title, body = collapse_repeated_headings(clean(read(path)))
        _, routes = parse_coverage(body)
        if not routes:
            continue
        found = UNIT_ID.search(next(iter(routes)))
        key = (found.group(1), found.group(2))
        block = blocks.get(key) or Block(key[0], key[1], title)
        block.title = block.title or title
        block.routes = routes
        blocks[key] = block

    for key, path in contracts.items():
        if key in blocks:
            _, record = collapse_repeated_headings(clean(read(path)))
            blocks[key].provenance = prose(re.sub(r"^#+\s+Provenance contract.*$", "", record, flags=re.MULTILINE).strip())

    for block in blocks.values():
        for unit in block.units:
            unit.statement = prose(unit.statement)
            unit.kind = prose(unit.kind)
        for route in block.routes.values():
            route.targets = prose(route.targets)
            route.comparison = prose(route.comparison)
            route.provenance = prose(route.provenance)

    known = set(blocks)
    pages: list[Page] = [render_block(b, known) for b in blocks.values()]

    by_source: dict[str, list[Block]] = {}
    for (source, _), block in blocks.items():
        by_source.setdefault(source, []).append(block)
    for source in by_source:
        by_source[source].sort(key=lambda b: block_order(b.name))

    for source, path in mapping_notes.items():
        title, body = collapse_repeated_headings(clean(read(path)))
        pages.append(Page(f"sources/{source.lower()}/mapping", title or f"{source} mapping", prose(body)))

    for source, group in by_source.items():
        extra = [p for p in pages if p.path == f"sources/{source.lower()}/mapping"]
        pages.append(render_source_index(source, group, intros.get(source, ""), extra))

    for stem, path in sorted(catalogues.items()):
        title, body = collapse_repeated_headings(clean(read(path)))
        pages.append(Page(f"catalogues/{stem}", title, prose(body)))
    for stem, path in sorted(other.items()):
        title, body = collapse_repeated_headings(clean(read(path)))
        pages.append(Page(f"notes/{stem}", title, prose(body)))
    for stem, out in (("foundational-source-corpus", "corpus"), ("foundational-corpus-status", "status")):
        title, body = collapse_repeated_headings(clean(read(notes[stem])))
        pages.append(Page(out, title, prose(body)))

    return by_source, pages


def block_order(name: str) -> tuple[int, str]:
    """Numbered chapters in order; lettered appendices after them."""
    if name.startswith("C") and name[1:].isdigit():
        return (int(name[1:]), "")
    return (10**6, name)


def write_section_indexes(pages: list[Page]) -> None:
    for section, title, blurb in (
        (
            "catalogues",
            "Definition catalogues",
            "Every definition a source states, in the order it states them, with the "
            "section and page it appears on. A catalogue is the completeness check on "
            "the enumeration: what the book defines, before any question of Lean.",
        ),
        (
            "notes",
            "Notes and audits",
            "Working records: source surveys, resolved ambiguities, and audits of this "
            "repository taken at a named commit. An audit describes the tree as it stood "
            "on its own date and is not maintained afterwards.",
        ),
    ):
        listed = sorted((p for p in pages if p.path.startswith(f"{section}/")), key=lambda p: p.title)
        lines = [blurb, ""]
        lines += [f"- [{p.title}]({p.path.split('/')[-1]}.html)" for p in listed]
        write(Page(f"{section}/index", title, "\n".join(lines)))


def write_coverage(by_source: dict[str, list[Block]]) -> Counter:
    grand = Counter()
    lines = [
        "Every definition, theorem, lemma, example and remark in a read chapter is a",
        "numbered unit. A swept chapter assigns each of its units exactly one route: a",
        "Lean declaration that owns the whole statement, or a finding that nothing does.",
        "",
        "Routes are strict about bundles. A unit is credited only when a checked",
        "declaration carries the statement the source makes, hypotheses included. A",
        "partial match is recorded as unmatched, with the partial named in its entry.",
        "",
        "| Source | Units | Swept | In Lean | Not in Lean |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for source, blocks in sorted(by_source.items()):
        counts = Counter()
        for block in blocks:
            counts.update(block.counts)
        grand.update(counts)
        routed = sum(counts.values())
        units = sum(len(b.units) or sum(b.counts.values()) for b in blocks)
        swept = sum(1 for b in blocks if b.counts)
        lines.append(
            f"| [{SOURCE_TITLES.get(source, source)}](sources/{source.lower()}/) | {units} | "
            f"{swept}/{len(blocks)} | {routed - counts['unmatched'] if routed else '—'} | "
            f"{counts['unmatched'] if routed else '—'} |"
        )
    lines += ["", "## Across every swept chapter", "", route_table(grand)]
    write(Page("coverage", "Coverage", "\n".join(lines)))
    return grand


def write_index(grand: Counter, by_source: dict[str, list[Block]]) -> None:
    units = sum(len(b.units) or sum(b.counts.values()) for blocks in by_source.values() for b in blocks)
    routed = sum(grand.values())
    body = f"""
Sixteen standard graduate mathematics textbooks, read cover to cover. Every
definition, theorem, lemma, example and remark is recorded as a numbered unit
carrying its statement and the page it appears on — **{units:,} of them so far** —
and where a chapter has been swept, each unit also names the Lean declaration
that owns it, or records that none does.

Read a chapter and you get the mathematics of that chapter with the state of its
formalization attached, statement by statement. Every declaration name links to
its Mathlib documentation; every commit and pull request links to the code it
names.

| | |
| --- | ---: |
| Source units enumerated | **{units:,}** |
| Of those, routed against Lean | {routed:,} |
| Owned by Mathlib | {grand['mathlib']:,} |
| Owned by an external Lean development | {grand['reference-port'] + grand['package-import']:,} |
| Owned by this repository | {grand['project-existing']:,} |
| **No Lean owner found** | **{grand['unmatched']:,}** |

An unmatched unit is the interesting case: its entry names the partial machinery
that does exist and the gap that stops it closing the statement, so it reads as a
concrete formalization target rather than an absence.

## Where to start

- [Coverage](coverage.md) — every source and how far it has been taken.
- [The corpus](corpus.md) — which books, which editions, what scope, and the
  prerequisite order they are read in.
- [Sweep status](status.md) — the per-source progress table.
- [Definition catalogues](catalogues/) — what each book defines, before any
  question of Lean.

## What the routes mean

{route_table(grand)}

## Caveats

The sweep is a search, not a proof. An unmatched unit asserts that a documented
search found no owner on the revisions named in its entry — not that none exists.
Mathlib moves; an entry is only as current as the commits its chapter records.
Statements are compressed restatements of the source, not quotations, and where
one of them and the Lean disagree, the Lean is right.
"""
    write(Page("index", "The foundational corpus", body))


def write_quarto(by_source: dict[str, list[Block]]) -> None:
    lines = [
        "project:",
        "  type: website",
        "  output-dir: _site",
        "",
        "website:",
        '  title: "lean-categories · corpus"',
        '  description: "Graduate mathematics, statement by statement, against Lean."',
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
    for source, blocks in sorted(by_source.items()):
        lines += [
            f'          - section: "{source}"',
            f"            href: sources/{source.lower()}/index.md",
            "            contents:",
        ]
        if (SITE / f"sources/{source.lower()}/mapping.md").exists():
            lines.append(f"              - sources/{source.lower()}/mapping.md")
        for block in blocks:
            lines.append(f"              - {block.href}.md")
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
        "    toc-expand: false",
        "    grid:",
        "      sidebar-width: 300px",
        "      body-width: 900px",
        "    css: styles.css",
        "    link-external-newwindow: true",
        "",
    ]
    (SITE / "_quarto.yml").write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vault", type=Path, default=DEFAULT_VAULT)
    args = parser.parse_args()
    assert args.vault.is_dir(), f"vault reference directory not found: {args.vault}"

    for stale in ("sources", "catalogues", "notes"):
        shutil.rmtree(SITE / stale, ignore_errors=True)

    by_source, pages = build(args.vault)
    for page in pages:
        write(page)
    write_section_indexes(pages)
    grand = write_coverage(by_source)
    write_index(grand, by_source)
    write_quarto(by_source)

    units = sum(len(b.units) for blocks in by_source.values() for b in blocks)
    print(f"{len(pages)} pages · {units} enumerated units · {sum(grand.values())} routed")


if __name__ == "__main__":
    main()
