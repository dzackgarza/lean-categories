#!/usr/bin/env python3
"""Generate the derived foundational-corpus scheduling frontier.

The whole-source status ledger remains the only completion authority. This tool
derives scheduling state from the frozen Sweep-I catalogues and Sweep-II mapping
records; it never checks or infers a whole-source completion box.
"""

from __future__ import annotations

import argparse
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


UNIT_RE = re.compile(r"FC\d{2}-[A-Z0-9]+-U\d+")
HEADING_UNIT_RE = re.compile(r"^###\s+(FC\d{2}-[A-Z0-9]+-U\d+)\b")
ROUTES = {"mathlib", "project-existing", "package-import", "reference-port", "unmatched"}
DIRECT_ROUTES = {"mathlib", "project-existing"}
NEGATIVE_VERDICT_MARKERS = ("unmatched", "partial", "wrong interface", "missing")
POSITIVE_LEGACY_VERDICT_MARKERS = ("exact", "broad")
DEFINITION_MARKERS = ("definition", "construction", "convention", "notation", "terminology")
# Labels that unambiguously announce result content.  If one of these is the
# source-unit label, a word such as "constructions" appearing only in the title
# must not promote the row into Sweep III.
STRICT_RESULT_LABEL_MARKERS = (
    "lemma",
    "proposition",
    "theorem",
    "corollary",
    "comparison",
    "application",
    "result",
    "criterion",
    "porism",
    "vista",
    "addendum",
    "calculation",
)
# Sources for which the richer mixed-unit phase classification below has been
# checked against the canonical source/mapping records.  Do not silently apply
# an FC05 audit result to another corpus source: extend this set only together
# with that source's own phase-classification audit.
CONTENT_CLASSIFIED_DEFINITION_SOURCES = frozenset({"FC05"})
THEOREM_MARKERS = (
    "lemma",
    "proposition",
    "theorem",
    "corollary",
    "comparison",
    "example",
    "application",
    "result",
    "criterion",
    "remark",
    "porism",
    "vista",
    "addendum",
    "calculation",
)

# Sweep-I occasionally preserves Weibel's label "Construction" for a unit whose
# mathematical content is only an argument/result, not a construction of new
# data.  These exceptions are source-audited rather than inferred from the word
# "Construction" alone.  Keep this set small: new ambiguities should be resolved
# against the source before being added here.
RESULT_ONLY_DEFINITION_UNITS = frozenset(
    {
        # Construction 5.6.5 is the collapse argument deriving the Künneth short
        # exact sequence; it introduces no new object, map, predicate, or notation.
        "FC05-C05-U049",
        # 6.8.3 is the pair of low-degree exact sequences extracted from the LHS
        # spectral sequences; it is result content despite the Sweep-I label.
        "FC05-C06-U100",
        # The §7.4 augmentation-ideal passage applies Tor to an already-defined
        # short exact sequence and states the resulting isomorphisms/exact sequence.
        "FC05-C07-U030",
        # 7.5.3 likewise consists of the low-degree exact sequences extracted
        # from the Hochschild--Serre spectral sequences.
        "FC05-C07-U042",
        # The §9.4 Hodge/λ row is a theorem-level preview of the decomposition;
        # the actual Hodge-subcomplex definition is Definition 9.4.15 (C09-U072).
        "FC05-C09-U064",
        # The §9.8 convention merely reuses the already-defined mixed-complex
        # operator B to name the d¹ map of Connes' spectral sequence.  Existence
        # of that induced homology differential is result content, not new data.
        "FC05-C09-U122",
    }
)


@dataclass(frozen=True)
class Unit:
    unit_id: str
    kind: str
    dependencies: tuple[str, ...]


@dataclass(frozen=True)
class Mapping:
    verdict: str
    route: str | None
    source: str
    row: str

    @property
    def delivered(self) -> bool:
        """Whether the mapping already supplies a canonical usable owner."""
        verdict = self.verdict.lower()
        if any(marker in verdict for marker in NEGATIVE_VERDICT_MARKERS):
            return False
        if self.route is not None:
            return self.route in DIRECT_ROUTES

        # FC01 C00/C01 predate the explicit Route column. Positive legacy rows
        # are direct pinned/project matches unless provenance says the code only
        # exists in an external package/reference.
        row = self.row.lower()
        if "external package" in row or "reference-port" in row:
            return False
        return any(marker in verdict for marker in POSITIVE_LEGACY_VERDICT_MARKERS)

    @property
    def definition_only(self) -> bool:
        """Whether this direct owner discharges only a mixed unit's definition layer."""
        return "[definition-only]" in self.row.lower()

    @property
    def action(self) -> str:
        if self.delivered:
            return "reuse"
        if self.route == "reference-port":
            return "port"
        if self.route == "package-import":
            return "import"
        if self.route == "unmatched":
            return "author"
        if self.route in DIRECT_ROUTES:
            return "repair mapping/interface"
        return "resolve legacy mapping"


@dataclass(frozen=True)
class SourceStatus:
    source_id: str
    catalogue: bool
    mapping: bool
    definitions: bool
    theorems: bool


def clean_cell(cell: str) -> str:
    return cell.strip().strip("`").replace("**", "").strip()


def split_table_row(line: str) -> list[str]:
    # Unit IDs and kind columns precede source data, so pipes in later prose do
    # not disturb the fields used below. Catalogue dependencies are always the
    # final cell, so escaped pipes in source prose do not affect that field.
    return [clean_cell(cell) for cell in line.strip().strip("|").split("|")]


def dependencies(text: str) -> tuple[str, ...]:
    return tuple(dict.fromkeys(UNIT_RE.findall(text)))


def parse_catalogue(path: Path) -> list[Unit]:
    lines = path.read_text(encoding="utf-8").splitlines()
    units: list[Unit] = []
    seen: set[str] = set()

    # FC01/FC02 use one subsection per source unit.
    for index, line in enumerate(lines):
        match = HEADING_UNIT_RE.match(line)
        if match is None:
            continue
        unit_id = match.group(1)
        end = index + 1
        while end < len(lines) and HEADING_UNIT_RE.match(lines[end]) is None:
            end += 1
        kind = ""
        deps = ""
        for entry in lines[index + 1 : end]:
            entry_lower = entry.lower()
            if entry_lower.startswith("- **kind:**"):
                kind = entry.split(":**", 1)[1].strip().rstrip(".")
            elif entry_lower.startswith("- **dependencies:**"):
                deps = entry.split(":**", 1)[1].strip().rstrip(".")
        if not kind:
            raise ValueError(f"{path}: no kind for {unit_id}")
        units.append(Unit(unit_id, kind, dependencies(deps)))
        seen.add(unit_id)

    # FC03+ use Markdown tables. Track the kind-column index from each table
    # header; dependencies are consistently the final column.
    kind_index: int | None = None
    for line in lines:
        if not line.startswith("|"):
            continue
        cells = split_table_row(line)
        lowered = [cell.lower() for cell in cells]
        if cells and UNIT_RE.fullmatch(cells[0]) is None:
            if any(cell == "id" or cell.endswith(" id") for cell in lowered):
                kind_index = next(
                    (i for i, cell in enumerate(lowered) if cell == "kind" or cell.startswith("kind /")),
                    None,
                )
            continue
        if not cells or UNIT_RE.fullmatch(cells[0]) is None or cells[0] in seen:
            continue
        if kind_index is None or kind_index >= len(cells):
            raise ValueError(f"{path}: cannot locate kind column for {cells[0]}")
        units.append(Unit(cells[0], cells[kind_index], dependencies(cells[-1])))
        seen.add(cells[0])

    if not units:
        raise ValueError(f"{path}: no source units parsed")
    return units


def mapping_from_row(path: Path, line: str) -> tuple[str, Mapping] | None:
    if not line.startswith("|"):
        return None
    cells = split_table_row(line)
    if len(cells) < 2 or UNIT_RE.fullmatch(cells[0]) is None:
        return None

    verdict = cells[1]
    # Some legacy mapping verdict text contains unescaped `|x|` notation, which
    # shifts the physical Markdown cells before the route column. Route tokens
    # are closed vocabulary, so locate the first exact token after the verdict.
    route = next((cell for cell in cells[2:] if cell in ROUTES), None)
    verdict_lower = verdict.lower()
    looks_like_mapping = route is not None or any(
        marker in verdict_lower
        for marker in (*NEGATIVE_VERDICT_MARKERS, *POSITIVE_LEGACY_VERDICT_MARKERS)
    )
    if not looks_like_mapping:
        return None
    return cells[0], Mapping(verdict, route, path.name, line)


def mapping_rank(mapping: Mapping) -> tuple[bool, bool]:
    """Prefer explicit route rows, then realized project-local rows."""
    return (mapping.route is not None, mapping.route == "project-existing")


def parse_mappings(reference_dir: Path) -> dict[str, Mapping]:
    found: dict[str, Mapping] = {}
    for path in sorted(reference_dir.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        # A few canonical mapping records have adjacent Markdown rows serialized
        # onto one physical line as `... | | `FCxx-...``. Recover those logical
        # row boundaries without rewriting the canonical record.
        text = re.sub(r"\|\s+\|\s+(?=`?FC\d{2}-[A-Z0-9]+-U\d+)", "|\n| ", text)
        for line in text.splitlines():
            parsed = mapping_from_row(path, line)
            if parsed is None:
                continue
            unit_id, candidate = parsed
            previous = found.get(unit_id)
            if previous is None or mapping_rank(candidate) > mapping_rank(previous):
                found[unit_id] = candidate
                continue
            if mapping_rank(candidate) == mapping_rank(previous):
                if candidate.delivered != previous.delivered or (
                    candidate.route is not None
                    and previous.route is not None
                    and candidate.route != previous.route
                ):
                    raise ValueError(
                        f"conflicting mapping rows for {unit_id}: "
                        f"{previous.source} ({previous.route}, {previous.verdict}) vs "
                        f"{candidate.source} ({candidate.route}, {candidate.verdict})"
                    )
    return found


def checked(cell: str) -> bool:
    return "[x]" in cell.lower()


def parse_status(path: Path) -> list[SourceStatus]:
    statuses: list[SourceStatus] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| FC"):
            continue
        cells = split_table_row(line)
        if len(cells) < 6 or re.fullmatch(r"FC\d{2}", cells[0]) is None:
            continue
        statuses.append(
            SourceStatus(
                source_id=cells[0],
                catalogue=checked(cells[2]),
                mapping=checked(cells[3]),
                definitions=checked(cells[4]),
                theorems=checked(cells[5]),
            )
        )
    if not statuses:
        raise ValueError(f"{path}: no source status rows parsed")
    return statuses


def kind_label(kind: str) -> str:
    """Return the source-unit label, excluding the descriptive title.

    Catalogue rows conventionally separate the source label from the title by
    an em dash.  Phase classification must inspect that label, not arbitrary
    words in the title: e.g. a theorem titled "Derived and Koszul constructions
    ..." is still a theorem.
    """
    return kind.partition("—")[0].strip().lower()


def is_definition(unit: Unit, mapping: Mapping | None = None) -> bool:
    """Whether the source unit carries Sweep-III definitional content."""
    source_id = unit.unit_id.split("-", 1)[0]
    kind = unit.kind.lower()
    if source_id not in CONTENT_CLASSIFIED_DEFINITION_SOURCES:
        return any(marker in kind for marker in DEFINITION_MARKERS)
    if mapping is not None and mapping.definition_only:
        return True
    if unit.unit_id in RESULT_ONLY_DEFINITION_UNITS:
        return False
    label = kind_label(unit.kind)
    # An explicit definitional source label wins, including mixed labels such
    # as `Construction/result`; the theorem clause is classified separately.
    if any(marker in label for marker in DEFINITION_MARKERS):
        return True
    # Do not let descriptive theorem titles such as "Derived and Koszul
    # constructions ..." masquerade as definitions.
    if any(marker in label for marker in STRICT_RESULT_LABEL_MARKERS):
        return False
    # Examples and remarks sometimes introduce genuine notation/constructions
    # without using a Definition heading (e.g. FC05-C01-U029 and C02-U035).
    return any(marker in kind for marker in DEFINITION_MARKERS)


def is_theorem(unit: Unit) -> bool:
    kind = unit.kind.lower()
    # Mixed rows can contribute both a Sweep-III definition and a Sweep-IV
    # theorem clause; the definition sweep explicitly leaves theorem clauses to IV.
    return any(marker in kind for marker in THEOREM_MARKERS) or not any(
        marker in kind for marker in DEFINITION_MARKERS
    )


def source_file(reference_dir: Path, prefix: str, source_id: str) -> Path:
    matches = sorted(reference_dir.glob(f"{prefix}-{source_id.lower()}-*.md"))
    if len(matches) != 1:
        raise ValueError(f"expected one {prefix} file for {source_id}, found {len(matches)}")
    return matches[0]


def phase_units(
    phase: str, units: list[Unit], mappings: dict[str, Mapping]
) -> list[Unit]:
    if phase == "Definitions":
        return [unit for unit in units if is_definition(unit, mappings.get(unit.unit_id))]
    if phase == "Theorems":
        return [unit for unit in units if is_theorem(unit)]
    if phase == "Mapping":
        return units
    raise ValueError(f"unsupported frontier phase {phase}")


def unit_delivered(phase: str, unit: Unit, mappings: dict[str, Mapping]) -> bool:
    mapping = mappings.get(unit.unit_id)
    if phase == "Mapping":
        return mapping is not None
    if phase == "Theorems" and mapping is not None and mapping.definition_only:
        return False
    return mapping is not None and mapping.delivered


def phase_blocker(phase: str, status: SourceStatus, statuses: list[SourceStatus]) -> str:
    if phase == "Mapping" and not status.catalogue:
        return "Sweep I catalogue is not complete for this source."
    if phase == "Definitions" and not status.mapping:
        return "Sweep II mapping is not complete for this source."
    if phase == "Theorems":
        open_definitions = [entry.source_id for entry in statuses if not entry.definitions]
        if open_definitions:
            return "Sweep III is not complete corpus-wide: " + ", ".join(open_definitions) + "."
    return "none"


def mapping_label(mapping: Mapping | None, phase: str) -> str:
    if mapping is None:
        return "missing mapping record"
    route = mapping.route or "legacy-direct"
    if phase == "Theorems" and mapping.definition_only:
        return f"{route}; theorem clause pending"
    return f"{route}; {mapping.action}"


def unit_blockers(
    phase: str,
    unit: Unit,
    mappings: dict[str, Mapping],
    catalogue_index: dict[str, Unit],
) -> tuple[str, ...]:
    """Return phase-relevant prerequisites that do not yet have a usable owner.

    In the audited FC05 Definitions sweep, theorem-only source dependencies are
    not admissible blockers: Definitions must close before theorem work opens.
    Mixed dependencies that themselves carry definitional content still block
    until that definition layer has an owner.
    """
    source_id = unit.unit_id.split("-", 1)[0]
    blockers: list[str] = []
    for dep in unit.dependencies:
        if phase == "Definitions" and source_id in CONTENT_CLASSIFIED_DEFINITION_SOURCES:
            dep_unit = catalogue_index.get(dep)
            if dep_unit is not None and not is_definition(dep_unit, mappings.get(dep)):
                continue
        if dep not in mappings or not mappings[dep].delivered:
            blockers.append(dep)
    return tuple(blockers)


def next_open_units(
    phase: str,
    pending: list[Unit],
    mappings: dict[str, Mapping],
    catalogue_index: dict[str, Unit],
    limit: int,
) -> list[Unit]:
    """Choose the next executable units without losing source traversal order.

    Scan the whole pending population before applying the display limit.  If the
    first pending units are blocked, truncating first hides executable rows that
    occur later in source order.  If nothing is executable, retain the earliest
    blocked rows so the frontier exposes the dependency stop instead of printing
    an empty scheduling table.
    """
    ready = [
        unit
        for unit in pending
        if not unit_blockers(phase, unit, mappings, catalogue_index)
    ]
    return (ready if ready else pending)[:limit]


def compact_unit_ids(units: list[Unit]) -> str:
    """Render an exact source-order unit set as compact consecutive spans."""
    if not units:
        return "none"

    parts: list[str] = []
    start = units[0].unit_id
    previous = start
    for unit in units[1:]:
        current = unit.unit_id
        previous_match = re.fullmatch(r"(FC\d{2}-[A-Z0-9]+-U)(\d+)", previous)
        current_match = re.fullmatch(r"(FC\d{2}-[A-Z0-9]+-U)(\d+)", current)
        consecutive = (
            previous_match is not None
            and current_match is not None
            and previous_match.group(1) == current_match.group(1)
            and int(current_match.group(2)) == int(previous_match.group(2)) + 1
        )
        if consecutive:
            previous = current
            continue
        parts.append(f"`{start}`" if start == previous else f"`{start}`–`{previous}`")
        start = previous = current
    parts.append(f"`{start}`" if start == previous else f"`{start}`–`{previous}`")
    return ", ".join(parts)


def render(reference_dir: Path, limit: int) -> str:
    statuses = parse_status(reference_dir / "foundational-corpus-status.md")
    mappings = parse_mappings(reference_dir)
    catalogues = {
        status.source_id: parse_catalogue(
            source_file(reference_dir, "foundational-corpus-units", status.source_id)
        )
        for status in statuses
    }

    missing_mappings = [
        unit.unit_id
        for status in statuses
        if status.mapping
        for unit in catalogues[status.source_id]
        if unit.unit_id not in mappings
    ]

    open_cells: list[tuple[SourceStatus, str]] = []
    for status in statuses:
        if not status.mapping:
            open_cells.append((status, "Mapping"))
        if not status.definitions:
            open_cells.append((status, "Definitions"))
        if not status.theorems:
            open_cells.append((status, "Theorems"))

    lines = [
        "# Foundational corpus scheduling frontier",
        "",
        "<!-- Generated by scripts/foundational_frontier.py; do not hand-edit. -->",
        "",
        "This is derived scheduling output, not a completion ledger. Sweep completion is read only from "
        "`.agents/references/foundational-corpus-status.md`. The frontier is regenerated from the canonical "
        "Sweep-I unit catalogues and Sweep-II mapping records.",
        "",
        f"Current whole-source ledger: **{len(open_cells)} unticked Mapping/Definitions/Theorems cells**.",
        "A unit is shown as delivered here only when its mapping record supplies a non-partial `mathlib` or "
        "`project-existing` route (or an equivalent positive legacy direct row). `package-import`, "
        "`reference-port`, partial-interface, and `unmatched` rows remain scheduling work until their mapping "
        "record points to a canonical usable owner.",
        "",
    ]

    if missing_mappings:
        missing_by_source = Counter(unit_id[:4] for unit_id in missing_mappings)
        summary = ", ".join(
            f"{source_id}={count}" for source_id, count in sorted(missing_by_source.items())
        )
        lines.extend(
            [
                "Mapping-record coverage warning: the authoritative ledger has Mapping checked for sources "
                f"with **{len(missing_mappings)}** catalogue units lacking a parsed mapping row ({summary}). "
                "This derived report does not change those ledger boxes; affected units remain pending here.",
                "",
            ]
        )

    for status, phase in open_cells:
        units = phase_units(phase, catalogues[status.source_id], mappings)
        delivered = [unit for unit in units if unit_delivered(phase, unit, mappings)]
        pending = [unit for unit in units if not unit_delivered(phase, unit, mappings)]
        route_counts = Counter(
            (mappings[unit.unit_id].route or "legacy") if unit.unit_id in mappings else "missing"
            for unit in pending
        )
        counts = ", ".join(f"{key}={value}" for key, value in sorted(route_counts.items())) or "none"

        lines.extend(
            [
                f"## {status.source_id} — {phase}",
                "",
                f"Delivered/directly reusable by mapping: **{len(delivered)}/{len(units)}**; "
                f"pending realization: **{len(pending)}** ({counts}).",
                f"Delivered/direct-reuse spans: {compact_unit_ids(delivered)}.",
                f"Phase blocker: {phase_blocker(phase, status, statuses)}",
                "",
            ]
        )
        if not pending:
            lines.extend(["No per-unit residue remains; the whole-source ledger is still authoritative.", ""])
            continue

        catalogue_index = {unit.unit_id: unit for unit in catalogues[status.source_id]}
        next_units = next_open_units(phase, pending, mappings, catalogue_index, limit)
        if not next_units:
            raise ValueError(
                f"{status.source_id} {phase}: pending units exist but the scheduling table is empty"
            )

        lines.extend(
            [
                f"Next {len(next_units)} open units in source traversal order:",
                "",
                "| Unit | Kind | Prerequisites | Unit blockers | Mapping action |",
                "| --- | --- | --- | --- | --- |",
            ]
        )
        for unit in next_units:
            prerequisites = ", ".join(f"`{dep}`" for dep in unit.dependencies) or "—"
            blockers = unit_blockers(phase, unit, mappings, catalogue_index)
            blocker_text = (
                ", ".join(f"`{dep}`" for dep in blockers)
                if blockers
                else "ready by recorded prerequisites"
            )
            kind = unit.kind.replace("|", "\\|")
            lines.append(
                f"| `{unit.unit_id}` | {kind} | {prerequisites} | {blocker_text} | "
                f"{mapping_label(mappings.get(unit.unit_id), phase)} |"
            )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--references",
        type=Path,
        default=Path(".agents/references"),
        help="canonical agent-memory reference directory (default: .agents/references)",
    )
    parser.add_argument("--limit", type=int, default=5, help="open units to display per unticked cell")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    print(render(args.references, args.limit), end="")


if __name__ == "__main__":
    main()
