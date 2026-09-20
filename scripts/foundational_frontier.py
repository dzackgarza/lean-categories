#!/usr/bin/env python3
"""Generate the derived foundational-corpus scheduling frontier.

The whole-source status ledger remains the only completion authority. This tool
derives scheduling state from the frozen Sweep-I catalogues and Sweep-II mapping
records; it never checks or infers a whole-source completion box.

Mapping may add an exact construction edge with one sentence-final clause:
"Construction prerequisites: `FCxx-Cyy-Uzzz`, `...`." Other cited IDs are inert.
"""

from __future__ import annotations

import argparse
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


UNIT_RE = re.compile(r"FC\d{2}-[A-Z0-9]+-U\d+")
HEADING_UNIT_RE = re.compile(r"^###\s+(FC\d{2}-[A-Z0-9]+-U\d+)\b")
CONSTRUCTION_PREREQUISITES_MARKER = "Construction prerequisites:"
CONSTRUCTION_PREREQUISITES_RE = re.compile(
    r"Construction prerequisites:\s+"
    r"(`FC\d{2}-[A-Z0-9]+-U\d+`(?:,\s*`FC\d{2}-[A-Z0-9]+-U\d+`)*)\.\s*$"
)
ROUTES = {"mathlib", "project-existing", "package-import", "reference-port", "unmatched"}
DIRECT_ROUTES = {"mathlib", "project-existing"}
NEGATIVE_VERDICT_MARKERS = ("unmatched", "wrong interface", "missing")
NEGATIVE_PARTIAL_VERDICT_PATTERNS = (
    r"^\s*partial(?:\s|$)",
    r"\bpartially\b",
    r"\bpartial\s+(?:match|comparison|interface|owner|route|implementation|formalization|coverage|clause)\b",
    r"\bremains?\s+partial\b",
)
RESULT_LAYER_MARKERS = (
    "theorem clause",
    "theorem content",
    "theorem work",
    "result clause",
    "result content",
    "result layer",
    "construction theorems",
)
RESULT_LAYER_PATTERNS = (
    r"\b(?:theorem|result|example|comparison|classification)(?:/[a-z-]+)?\s+"
    r"(?:clause|clauses|content|work|assertion|assertions)\b",
    r"\b(?:theorem|result|example)/(?:theorem|result|example)\s+clauses?\b",
)


def is_negative_verdict(verdict: str) -> bool:
    """Recognize evaluative negative verdicts without matching mathematical `partial` terms.

    `partial flow`, `partial zeta`, and `partial Hecke theta` are mathematical nouns, not
    Mapping status.  Older code used the raw substring `partial`, which turned such positive
    direct routes into spurious `review` work.
    """

    value = verdict.lower()
    return any(marker in value for marker in NEGATIVE_VERDICT_MARKERS) or any(
        re.search(pattern, value) is not None for pattern in NEGATIVE_PARTIAL_VERDICT_PATTERNS
    )
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
# Every admitted source now carries source-audited phase labels.  Classification
# uses the label before the descriptive title, so theorem/result prose appearing
# later in a title cannot promote a result-only unit into Sweep III.
CONTENT_CLASSIFIED_DEFINITION_SOURCES = frozenset({f"FC{i:02d}" for i in range(1, 18)})
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

@dataclass(frozen=True)
class Unit:
    unit_id: str
    kind: str
    source_data: str
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
        if self.realized:
            # Sweep-II provenance is causal and does not change when a later
            # port/import/greenfield definition is realized.  `[realized]`
            # therefore closes Sweep III without rewriting the historical
            # route to `project-existing`.
            return True
        verdict = self.verdict.lower()
        if is_negative_verdict(verdict):
            return False
        if self.route is not None:
            return self.route in DIRECT_ROUTES or self.realized

        # FC01 C00/C01 predate the explicit Route column. Positive legacy rows
        # are direct pinned/project matches unless provenance says the code only
        # exists in an external package/reference.
        row = self.row.lower()
        if "external package" in row or "reference-port" in row:
            return False
        return any(marker in verdict for marker in POSITIVE_LEGACY_VERDICT_MARKERS)

    @property
    def realized(self) -> bool:
        """Whether a mapped port/import has already been realized locally."""
        return "[realized]" in self.row.lower()

    @property
    def definition_only(self) -> bool:
        """Whether this direct owner discharges only a mixed unit's definition layer."""
        return "[definition-only]" in self.row.lower()

    @property
    def sweep_iii_blocked(self) -> bool:
        """Whether this named object still requires result-layer input.

        A mixed source row can have its raw carrier realized in Sweep III while
        a later definition/convention depends on a theorem about that carrier.
        The explicit marker keeps the later unit out of the executable
        Definitions frontier without pretending that the carrier realization
        itself is undelivered.
        """
        return "[sweep-iii-blocked]" in self.row.lower()

    @property
    def negative_search_complete(self) -> bool:
        """Whether an unmatched row has passed the finite negative-search gate."""

        return "[negative-search-complete]" in self.row.lower()

    @property
    def residue_search_audited(self) -> bool:
        """Whether a negative definition survived the open-ended prior-art audit."""

        return "[residue-search-audited]" in self.row.lower()

    @property
    def action(self) -> str:
        if self.delivered:
            return "reuse"
        if self.route == "reference-port":
            return "port"
        if self.route == "package-import":
            return "import"
        if self.route == "unmatched":
            return "author" if self.residue_search_audited else "residue audit"
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
    # Split only on actual Markdown delimiters.  Source prose frequently
    # contains LaTeX `\|` (for norms, field extensions, restrictions, etc.);
    # treating those pipes as column separators silently truncates the
    # mathematical statement and poisons downstream retrieval queries.
    text = line.strip().strip("|")
    cells: list[str] = []
    start = 0
    for index, character in enumerate(text):
        if character == "|" and (index == 0 or text[index - 1] != "\\"):
            cells.append(text[start:index])
            start = index + 1
    cells.append(text[start:])
    return [clean_cell(cell) for cell in cells]


def dependencies(text: str) -> tuple[str, ...]:
    return tuple(dict.fromkeys(UNIT_RE.findall(text)))


def construction_dependencies(unit: Unit, mapping: Mapping | None) -> tuple[str, ...]:
    """Parse Mapping's explicit construction-prerequisite annotation.

    Other unit IDs in Mapping are provenance, comparisons, or historical notes
    and never become scheduler edges implicitly.
    """
    if mapping is None or CONSTRUCTION_PREREQUISITES_MARKER not in mapping.row:
        return ()

    if mapping.row.count(CONSTRUCTION_PREREQUISITES_MARKER) != 1:
        raise ValueError(
            f"{unit.unit_id}: expected exactly one sentence-final "
            f"{CONSTRUCTION_PREREQUISITES_MARKER} annotation"
        )

    annotated_cells = [
        cell
        for cell in split_table_row(mapping.row)
        if CONSTRUCTION_PREREQUISITES_MARKER in cell
    ]
    if len(annotated_cells) != 1:
        raise ValueError(
            f"{unit.unit_id}: expected exactly one sentence-final "
            f"{CONSTRUCTION_PREREQUISITES_MARKER} annotation"
        )
    match = CONSTRUCTION_PREREQUISITES_RE.search(annotated_cells[0])
    if match is None:
        raise ValueError(
            f"{unit.unit_id}: malformed {CONSTRUCTION_PREREQUISITES_MARKER} annotation; "
            "use comma-separated backticked full unit IDs and a final period"
        )
    return tuple(dict.fromkeys(UNIT_RE.findall(match.group(1))))


def effective_dependencies(
    phase: str, unit: Unit, mapping: Mapping | None
) -> tuple[str, ...]:
    """Combine catalogue edges with explicit construction edges for Definitions."""
    if phase != "Definitions":
        return unit.dependencies
    return tuple(
        dict.fromkeys((*unit.dependencies, *construction_dependencies(unit, mapping)))
    )


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
        source_data = ""
        deps = ""
        for entry in lines[index + 1 : end]:
            entry_lower = entry.lower()
            if entry_lower.startswith("- **kind:**"):
                kind = entry.split(":**", 1)[1].strip().rstrip(".")
            elif entry_lower.startswith("- **statement/data:**"):
                source_data = entry.split(":**", 1)[1].strip().rstrip(".")
            elif entry_lower.startswith("- **dependencies:**"):
                deps = entry.split(":**", 1)[1].strip().rstrip(".")
        if not kind:
            raise ValueError(f"{path}: no kind for {unit_id}")
        if not source_data:
            raise ValueError(f"{path}: no statement/data for {unit_id}")
        units.append(Unit(unit_id, kind, source_data, dependencies(deps)))
        seen.add(unit_id)

    # FC03+ use Markdown tables. Track the kind-column index from each table
    # header; dependencies are consistently the final column.
    kind_index: int | None = None
    data_index: int | None = None
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
                data_index = next(
                    (
                        i
                        for i, cell in enumerate(lowered)
                        if cell
                        in {
                            "unit / hypotheses-data",
                            "mathematical unit",
                            "concise data",
                            "concise data / hypotheses",
                            "canonical statement / definition",
                            "data / hypotheses",
                            "source statement",
                        }
                    ),
                    None,
                )
            continue
        if not cells or UNIT_RE.fullmatch(cells[0]) is None or cells[0] in seen:
            continue
        if kind_index is None or kind_index >= len(cells):
            raise ValueError(f"{path}: cannot locate kind column for {cells[0]}")
        if data_index is None or data_index >= len(cells):
            raise ValueError(f"{path}: cannot locate source-data column for {cells[0]}")
        units.append(
            Unit(cells[0], cells[kind_index], cells[data_index], dependencies(cells[-1]))
        )
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
    looks_like_mapping = (
        route is not None
        or is_negative_verdict(verdict_lower)
        or any(marker in verdict_lower for marker in POSITIVE_LEGACY_VERDICT_MARKERS)
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


def is_theorem(unit: Unit, mapping: Mapping | None = None) -> bool:
    kind = unit.kind.lower()
    # Mixed rows can contribute both a Sweep-III definition and a Sweep-IV
    # theorem clause; the definition sweep explicitly leaves theorem clauses to IV.
    # `[definition-only]` is itself a source-audited assertion that the positive
    # mapping discharges only the definitional part, so it must force the row into
    # Sweep IV even when Sweep I gave it a plain `Definition / construction` label.
    return (mapping is not None and (mapping.definition_only or mapping.sweep_iii_blocked)) or any(
        marker in kind for marker in THEOREM_MARKERS
    ) or not any(
        marker in kind for marker in DEFINITION_MARKERS
    )


def mapping_declares_result_layer(mapping: Mapping | None) -> bool:
    """Whether Mapping explicitly records theorem/result content in this source unit."""

    if mapping is None:
        return False
    row = mapping.row.lower()
    return any(marker in row for marker in RESULT_LAYER_MARKERS) or any(
        re.search(pattern, row) is not None for pattern in RESULT_LAYER_PATTERNS
    )


def validate_phase_classification(units: list[Unit], mappings: dict[str, Mapping]) -> None:
    """Reject source rows whose recorded result layer would disappear from Sweep IV.

    Mapping is allowed to split a mixed source unit into a definition route plus
    later theorem work, but the frozen Sweep-I kind must still expose that mixed
    role.  Otherwise a bad catalogue label silently promotes propositions into
    Sweep III or drops them from Sweep IV.
    """

    defects = [
        unit
        for unit in units
        if mapping_declares_result_layer(mappings.get(unit.unit_id))
        and not is_theorem(unit, mappings.get(unit.unit_id))
    ]
    if defects:
        rendered = ", ".join(f"{unit.unit_id} ({unit.kind})" for unit in defects)
        raise ValueError(
            "source/mapping phase-classification mismatch: Mapping records a "
            f"theorem/result layer but Sweep IV would omit {rendered}"
        )

    erased_residue_audits = [
        unit
        for unit in units
        if (mapping := mappings.get(unit.unit_id)) is not None
        and mapping.route == "unmatched"
        and not mapping.residue_search_audited
        and (
            mapping.realized
            or (
                mapping.definition_only
                and "local source transcription" in mapping.row.lower()
            )
        )
    ]
    if erased_residue_audits:
        rendered = ", ".join(unit.unit_id for unit in erased_residue_audits)
        raise ValueError(
            "Sweep-III realization erased State-1 residue-search provenance for "
            f"{rendered}; unmatched realization must preserve "
            "[residue-search-audited] and append realization state instead"
        )

    exercise_leaks = [
        unit
        for unit in units
        if is_definition(unit, mappings.get(unit.unit_id))
        and re.search(r"\bexercise\b", f"{unit.kind} {unit.source_data}", re.I)
    ]
    if exercise_leaks:
        rendered = ", ".join(unit.unit_id for unit in exercise_leaks)
        raise ValueError(
            "excluded exercise material leaked into Sweep III source payload: "
            f"{rendered}"
        )

    known_unit_ids = {unit.unit_id for unit in units}
    for unit in units:
        explicit_dependencies = construction_dependencies(
            unit, mappings.get(unit.unit_id)
        )
        unknown = [dep for dep in explicit_dependencies if dep not in known_unit_ids]
        if unknown:
            rendered = ", ".join(unknown)
            raise ValueError(
                f"{unit.unit_id}: construction prerequisites are not catalogue units: "
                f"{rendered}"
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
        return [unit for unit in units if is_theorem(unit, mappings.get(unit.unit_id))]
    if phase == "Mapping":
        # Sweep-II ultimately maps every corpus unit, but only definitional rows
        # can force Sweep III to invent an object.  Discovery for that gate is
        # therefore definition-focused even for a newly admitted source.  Theorem
        # mapping remains an obligation and is visible when Sweep IV opens; it is
        # not allowed to serialize the definition layer behind thousands of
        # unrelated theorem/remark/example searches.
        return [unit for unit in units if is_definition(unit, mappings.get(unit.unit_id))]
    raise ValueError(f"unsupported frontier phase {phase}")


def mapping_row_coverage_incomplete(
    units: list[Unit], mappings: dict[str, Mapping]
) -> bool:
    """Whether the source's definition layer lacks a canonical mapping row."""

    return any(
        is_definition(unit, mappings.get(unit.unit_id)) and unit.unit_id not in mappings
        for unit in units
    )


def definition_mapping_incomplete(
    units: list[Unit], mappings: dict[str, Mapping]
) -> bool:
    """Whether any definition still lacks an accepted reuse/negative disposition."""

    for unit in units:
        mapping = mappings.get(unit.unit_id)
        if not is_definition(unit, mapping):
            continue
        if mapping is None:
            return True
        if mapping.route == "unmatched" and not mapping.residue_search_audited:
            return True
    return False


def unit_delivered(phase: str, unit: Unit, mappings: dict[str, Mapping]) -> bool:
    mapping = mappings.get(unit.unit_id)
    if phase == "Mapping":
        # A reference/package route completes Mapping even when later realization
        # still needs a port/import.  Only absent records and explicit `unmatched`
        # verdicts remain source-discovery work here.
        return mapping is not None and (
            mapping.route != "unmatched" or mapping.residue_search_audited
        )
    if phase == "Theorems" and mapping is not None and mapping.definition_only:
        return False
    return mapping is not None and mapping.delivered


def phase_blocker(
    phase: str,
    status: SourceStatus,
    statuses: list[SourceStatus],
    units: list[Unit],
    mappings: dict[str, Mapping],
    catalogues: dict[str, list[Unit]],
) -> str:
    if phase == "Mapping" and not status.catalogue:
        return "Sweep I catalogue is not complete for this source."
    if phase == "Definitions":
        open_definition_mapping = [
            source_id
            for source_id, source_units in catalogues.items()
            if definition_mapping_incomplete(source_units, mappings)
        ]
        if open_definition_mapping:
            return (
                "Milestone 1 is open: definitional mapping/residue audit remains for "
                + ", ".join(open_definition_mapping)
                + "."
            )
    if phase == "Theorems":
        open_definitions = [entry.source_id for entry in statuses if not entry.definitions]
        if open_definitions:
            return "Sweep III is not complete corpus-wide: " + ", ".join(open_definitions) + "."
    return "none"


def mapping_label(mapping: Mapping | None, phase: str) -> str:
    if mapping is None:
        return "missing mapping record"
    route = mapping.route or "legacy-direct"
    if phase == "Mapping":
        if mapping.route == "unmatched":
            if mapping.residue_search_audited:
                return "unmatched; residue search audited"
            if mapping.negative_search_complete:
                return "unmatched; open-ended residue audit required"
            return "unmatched; search existing formalizations"
        return f"{route}; source already found"
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

    Catalogue theorem edges do not ordinarily block Definitions: Definitions
    must close before theorem work opens. Mapping may preserve a theorem or
    definition that constructs the named output through the explicit
    `Construction prerequisites:` annotation.
    """
    if phase == "Mapping":
        # Discovery of an existing implementation does not depend on whether a
        # prerequisite unit has itself been realized locally.
        return ()

    mapping = mappings.get(unit.unit_id)
    if phase == "Definitions" and mapping is not None and mapping.sweep_iii_blocked:
        return ("Sweep-IV result layer",)

    source_id = unit.unit_id.split("-", 1)[0]
    explicit_dependencies = construction_dependencies(unit, mapping)
    blockers: list[str] = []
    for dep in effective_dependencies(phase, unit, mapping):
        if phase == "Definitions" and source_id in CONTENT_CLASSIFIED_DEFINITION_SOURCES:
            dep_unit = catalogue_index.get(dep)
            if (
                dep not in explicit_dependencies
                and dep_unit is not None
                and not is_definition(dep_unit, mappings.get(dep))
            ):
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
    validate_phase_classification(
        [unit for source_units in catalogues.values() for unit in source_units],
        mappings,
    )

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
        "`corpus/foundational-corpus-status.md`. The frontier is regenerated from the canonical "
        "Sweep-I unit catalogues and Sweep-II mapping records.",
        "",
        f"Current whole-source ledger: **{len(open_cells)} unticked Mapping/Definitions/Theorems cells**.",
        "For Mapping, a definitional unit is complete once it has a positive implementation source: "
        "`mathlib`, `project-existing`, `package-import`, or `reference-port`; only missing/`unmatched` "
        "definitions remain discovery work. For Definitions and Theorems, realization is stricter: "
        "`reference-port`, `package-import`, partial-interface, and `unmatched` rows can still require work.",
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
        source_units = catalogues[status.source_id]
        initial_mapping_coverage = (
            phase == "Mapping"
            and mapping_row_coverage_incomplete(source_units, mappings)
        )
        units = phase_units(phase, source_units, mappings)
        if initial_mapping_coverage:
            # During initial row coverage, every explicit route — including an
            # exhaustively searched `unmatched` verdict — is a delivered Sweep-II
            # record.  The later definition-focused correction reopens only the
            # unmatched definitional rows after complete row coverage exists.
            delivered = [unit for unit in units if unit.unit_id in mappings]
            pending = [unit for unit in units if unit.unit_id not in mappings]
        else:
            delivered = [unit for unit in units if unit_delivered(phase, unit, mappings)]
            pending = [unit for unit in units if not unit_delivered(phase, unit, mappings)]
        route_counts = Counter(
            (mappings[unit.unit_id].route or "legacy") if unit.unit_id in mappings else "missing"
            for unit in pending
        )
        counts = ", ".join(f"{key}={value}" for key, value in sorted(route_counts.items())) or "none"

        if phase == "Mapping":
            if initial_mapping_coverage:
                summary_lines = [
                    f"## {status.source_id} — {phase}",
                    "",
                    f"Canonical mapping rows present: **{len(delivered)}/{len(units)}**; "
                    f"row-coverage gaps: **{len(pending)}** ({counts}).",
                    f"Mapped source-unit spans: {compact_unit_ids(delivered)}.",
                    f"Phase blocker: {phase_blocker(phase, status, statuses, source_units, mappings, catalogues)}",
                    "",
                ]
            else:
                summary_lines = [
                    f"## {status.source_id} — {phase}",
                    "",
                    f"Definitions with an implementation source: **{len(delivered)}/{len(units)}**; "
                    f"source-discovery gaps: **{len(pending)}** ({counts}).",
                    f"Already-sourced definition spans: {compact_unit_ids(delivered)}.",
                    f"Phase blocker: {phase_blocker(phase, status, statuses, source_units, mappings, catalogues)}",
                    "",
                ]
        else:
            summary_lines = [
                f"## {status.source_id} — {phase}",
                "",
                f"Delivered/directly reusable by mapping: **{len(delivered)}/{len(units)}**; "
                f"pending realization: **{len(pending)}** ({counts}).",
                f"Delivered/direct-reuse spans: {compact_unit_ids(delivered)}.",
                f"Phase blocker: {phase_blocker(phase, status, statuses, source_units, mappings, catalogues)}",
                "",
            ]
        lines.extend(summary_lines)
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
            prerequisites = ", ".join(
                f"`{dep}`"
                for dep in effective_dependencies(
                    phase, unit, mappings.get(unit.unit_id)
                )
            ) or "—"
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
        default=Path("corpus"),
        help="canonical tracked corpus reference directory (default: corpus)",
    )
    parser.add_argument("--limit", type=int, default=5, help="open units to display per unticked cell")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    print(render(args.references, args.limit), end="")


if __name__ == "__main__":
    main()
