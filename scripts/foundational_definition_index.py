#!/usr/bin/env python3
"""Generate the corpus-wide foundational definition discovery table.

This is a derived search/work surface, not another completion ledger.  It joins
the canonical Sweep-I catalogues to the canonical Sweep-II mapping records and
puts every definitional obligation in one table so ecosystem discovery can be
done in bulk instead of source-by-source.
"""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path
from typing import Iterable

import foundational_frontier as frontier


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = REPOSITORY_ROOT / "corpus"
DEFAULT_OUTPUT = REPOSITORY_ROOT / "FOUNDATIONAL_DEFINITIONS.tsv"


def clean_markdown(text: str) -> str:
    """Collapse table/Markdown noise while preserving mathematical spelling."""

    text = text.replace("`", "").replace("**", "")
    text = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", text)
    return " ".join(text.split()).strip()


def unit_metadata(path: Path) -> dict[str, tuple[str, str, str]]:
    """Return label, location, and searchable source data for every unit."""

    result: dict[str, tuple[str, str, str]] = {}
    lines = path.read_text(encoding="utf-8").splitlines()

    heading_starts: list[tuple[int, str, str]] = []
    for index, line in enumerate(lines):
        match = frontier.HEADING_UNIT_RE.match(line)
        if match is not None:
            unit_id = match.group(1)
            tail = line[match.end() :].strip().lstrip("—-").strip()
            label = clean_markdown(tail) or unit_id
            result[unit_id] = (label, "", label)
            heading_starts.append((index, unit_id, label))

    # FC01/FC02 use heading records rather than tables.  Their exact source
    # sentence is already present under `Statement/data`; retain it for bulk
    # retrieval instead of reducing those units to a slug or bare source ID.
    for position, (start, unit_id, label) in enumerate(heading_starts):
        end = heading_starts[position + 1][0] if position + 1 < len(heading_starts) else len(lines)
        location = ""
        data = ""
        for entry in lines[start + 1 : end]:
            lowered = entry.lower()
            if lowered.startswith("- **locator:**"):
                location = clean_markdown(entry.split(":**", 1)[1])
            elif lowered.startswith("- **statement/data:**"):
                data = clean_markdown(entry.split(":**", 1)[1])
        result[unit_id] = (label, location, data or label)

    headers: list[str] | None = None
    for line in lines:
        if not line.startswith("|"):
            continue
        cells = frontier.split_table_row(line)
        lowered = [cell.lower() for cell in cells]
        if cells and frontier.UNIT_RE.fullmatch(cells[0]) is None:
            if any(cell == "id" or cell.endswith(" id") for cell in lowered):
                headers = lowered
            continue
        if not cells or frontier.UNIT_RE.fullmatch(cells[0]) is None:
            continue
        unit_id = cells[0]
        if headers is None:
            label = cells[2] if len(cells) > 2 else unit_id
            location = cells[3] if len(cells) > 3 else ""
        elif "kerodon tag" in headers:
            tag_index = headers.index("kerodon tag")
            name_index = headers.index("explicit name")
            reference_index = headers.index("reference")
            context_index = headers.index("section context")
            tag = clean_markdown(cells[tag_index])
            name = clean_markdown(cells[name_index])
            label = name if name and name != "—" else f"Kerodon {tag}"
            reference = clean_markdown(cells[reference_index])
            context = clean_markdown(cells[context_index])
            location = "; ".join(part for part in (reference, context) if part)
        else:
            label_index = next(
                (
                    i
                    for i, value in enumerate(headers)
                    if value in {"unit", "source unit", "statement", "title"}
                    or "source unit" in value
                    or value.startswith("unit /")
                ),
                2 if len(cells) > 2 else 0,
            )
            location_index = next(
                (
                    i
                    for i, value in enumerate(headers)
                    if value in {"source", "location", "source location"}
                ),
                3 if len(cells) > 3 else 0,
            )
            label = cells[label_index] if label_index < len(cells) else unit_id
            location = cells[location_index] if location_index < len(cells) else ""
        data_index = next(
            (
                i
                for i, value in enumerate(headers or [])
                if value in {
                    "mathematical unit",
                    "unit / hypotheses-data",
                    "concise data",
                    "concise data / hypotheses",
                    "canonical statement / definition",
                    "data / hypotheses",
                }
            ),
            None,
        )
        data = cells[data_index] if data_index is not None and data_index < len(cells) else label
        # FC17 deliberately stores only a source-statement link in the table;
        # the live statement is handled by the Kerodon query enrichment pass,
        # not by treating the word "statement" as mathematical content.
        if headers is not None and "kerodon tag" in headers:
            data = label
        result[unit_id] = (
            clean_markdown(label),
            clean_markdown(location),
            clean_markdown(data),
        )
    return result


GENERIC_SEARCH_WORDS = {
    "comparison",
    "construction",
    "convention",
    "definition",
    "definitions",
    "interpretation",
    "notation",
    "terminology",
}


def search_key(label: str, data: str) -> str:
    """Derive a compact first-pass discovery query from a catalogue label."""

    if frontier.UNIT_RE.fullmatch(label):
        return data or label

    value = re.sub(
        r"^(?:Definition|Construction|Convention|Notation|Terminology)\b"
        r"(?:\s+[A-Za-z0-9.*-]+)?\s*(?:—|-|:)?\s*",
        "",
        label,
        flags=re.IGNORECASE,
    ).strip()
    value = re.sub(r"\([^)]*FC\d+[^)]*\)", "", value).strip()
    tokens = re.findall(r"[A-Za-z]+|\d+", value)
    substantive = [
        token
        for token in tokens
        if token.lower() not in GENERIC_SEARCH_WORDS
        and not token.isdigit()
        and re.fullmatch(r"[IVXLCDM]+", token.upper()) is None
    ]
    if substantive:
        return value

    # Several canonical catalogues use a generic `Kind / source unit` column
    # but already carry the actual mathematical sentence in `Concise data` (or
    # its equivalent).  Search that source data rather than manufacturing an
    # empty `/ construction` query from the kind label.
    return data or value or label


def rows(corpus: Path) -> Iterable[list[str]]:
    """Yield one joined row for every Sweep-III definitional unit."""

    statuses = frontier.parse_status(corpus / "foundational-corpus-status.md")
    mappings = frontier.parse_mappings(corpus)
    for status in statuses:
        catalogue = frontier.source_file(
            corpus, "foundational-corpus-units", status.source_id
        )
        metadata = unit_metadata(catalogue)
        for unit in frontier.parse_catalogue(catalogue):
            mapping = mappings.get(unit.unit_id)
            if not frontier.is_definition(unit, mapping):
                continue
            label, location, data = metadata.get(
                unit.unit_id, (unit.unit_id, "", unit.unit_id)
            )
            route = mapping.route if mapping is not None and mapping.route else "missing"
            # Reopening a source's Mapping phase reopens discovery for every
            # unmatched definition in that source.  An old
            # `[negative-search-complete]` marker remains the authoring gate
            # only after Mapping is closed again; while Mapping is open it is
            # prior evidence to recheck, not a reason to omit the row from the
            # bulk candidate census.
            if mapping is None or (
                route == "unmatched"
                and (not status.mapping or not mapping.negative_search_complete)
            ):
                action = "search"
            elif route == "unmatched":
                action = "author"
            elif route == "reference-port":
                action = "port"
            elif route == "package-import":
                action = "import"
            elif mapping.delivered:
                action = "reuse"
            else:
                action = "review"
            yield [
                unit.unit_id,
                status.source_id,
                unit.kind,
                label,
                location,
                data,
                route,
                action,
                search_key(label, data),
                mapping.verdict if mapping is not None else "",
                mapping.source if mapping is not None else "—",
            ]


def render(corpus: Path) -> str:
    """Return the deterministic TSV representation."""

    from io import StringIO

    buffer = StringIO()
    writer = csv.writer(buffer, dialect="excel-tab", lineterminator="\n")
    writer.writerow(
        [
            "unit_id",
            "source_id",
            "kind",
            "label",
            "source_location",
            "source_data",
            "route",
            "action",
            "search_key",
            "mapping_hint",
            "mapping_record",
        ]
    )
    writer.writerows(rows(corpus))
    return buffer.getvalue()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = render(args.corpus)
    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            raise SystemExit(f"stale generated definition index: {args.output}")
    else:
        args.output.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
