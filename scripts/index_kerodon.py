#!/usr/bin/env python3
"""Build and verify the supplementary Kerodon stable-tag index.

Kerodon exposes a hierarchy API for each part, but that API repeats tags when
an equation-like tag and a heading share a reference and omits a small number
of valid orphaned tags.  A refresh therefore:

1. downloads the three part trees and the official total from Kerodon;
2. deduplicates tree records by stable tag;
3. probes only allocator gaps below the greatest tree tag until the official
   total is reached; and
4. writes a normalized JSON snapshot and a generated Markdown catalogue.

The checked-in snapshot stores metadata and source locations only.  It does
not mirror Kerodon's statement or proof prose.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import sys
import tempfile
import time
import urllib.error
import urllib.request
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SNAPSHOT = REPOSITORY_ROOT / "corpus" / "kerodon-source-units.json"
DEFAULT_OUTPUT = REPOSITORY_ROOT / "corpus" / "kerodon-source-unit-index.md"

BASE_URL = "https://kerodon.net"
PART_TAGS = ("0000", "02GZ", "00FP")
RETIRED_PART_TAG = "00FP"
STRUCTURAL_KINDS = frozenset(
    {"part", "chapter", "section", "subsection", "subsubsection"}
)

# Kerodon inherits the Stacks-style ambiguity-free tag alphabet: I and O are
# omitted.  The order is needed only to find holes below the greatest tag that
# occurs in the public part trees.
TAG_ALPHABET = "0123456789ABCDEFGHJKLMNPQRSTUVWXYZ"
TAG_PATTERN = re.compile(r"^[0-9A-HJ-NP-Z]{4}$")
TOTAL_PATTERN = re.compile(r"There are\s+(\d+)\s+tags in total\.")
TITLE_PATTERN = re.compile(
    r"^(?P<kind>[A-Za-z]+)\s+(?P<reference>[0-9]+(?:\.[0-9]+)*)\s+"
    r"\((?P<tag>[0-9A-HJ-NP-Z]{4})\)—Kerodon$"
)
TITLE_HTML_PATTERN = re.compile(r"<title>(.*?)</title>", re.DOTALL | re.IGNORECASE)

SCHEMA_VERSION = 1
USER_AGENT = (
    "lean-categories Kerodon metadata indexer/1 "
    "(https://github.com/dzackgarza/lean-categories)"
)


class IndexErrorWithContext(RuntimeError):
    """A malformed or incomplete source/index condition."""


def utc_now() -> str:
    """Return the current UTC time in the snapshot's canonical format."""

    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def sha256(data: bytes) -> str:
    """Return the hexadecimal SHA-256 digest of *data*."""

    return hashlib.sha256(data).hexdigest()


def fetch_bytes(path: str, *, attempts: int = 3) -> bytes:
    """Fetch a Kerodon path with bounded retries and an identifying agent."""

    request = urllib.request.Request(
        BASE_URL + path,
        headers={"User-Agent": USER_AGENT, "Accept": "text/html,application/json"},
    )
    last_error: BaseException | None = None
    for attempt in range(1, attempts + 1):
        try:
            with urllib.request.urlopen(request, timeout=120) as response:
                return response.read()
        except (TimeoutError, urllib.error.URLError) as error:
            last_error = error
            if attempt != attempts:
                time.sleep(attempt)
    raise IndexErrorWithContext(f"failed to fetch {request.full_url}: {last_error}")


def tag_number(tag: str) -> int:
    """Decode a four-character Kerodon tag in allocator order."""

    if TAG_PATTERN.fullmatch(tag) is None:
        raise IndexErrorWithContext(f"invalid Kerodon tag {tag!r}")
    value = 0
    for character in tag:
        value = value * len(TAG_ALPHABET) + TAG_ALPHABET.index(character)
    return value


def tag_from_number(value: int) -> str:
    """Encode a nonnegative allocator index as a four-character tag."""

    if value < 0:
        raise IndexErrorWithContext(f"negative tag index {value}")
    characters: list[str] = []
    quotient = value
    for _ in range(4):
        quotient, remainder = divmod(quotient, len(TAG_ALPHABET))
        characters.append(TAG_ALPHABET[remainder])
    if quotient != 0:
        raise IndexErrorWithContext(f"tag index {value} exceeds four characters")
    return "".join(reversed(characters))


def normalize_tree_record(node: Mapping[str, Any], part_tag: str) -> dict[str, Any]:
    """Normalize one hierarchy node, excluding recursively embedded children."""

    required = ("tag", "type", "reference")
    missing = [field for field in required if field not in node]
    if missing:
        raise IndexErrorWithContext(
            f"tree record is missing {', '.join(missing)}: {node!r}"
        )
    record: dict[str, Any] = {
        "tag": str(node["tag"]),
        "reference": str(node["reference"]),
        "kind": str(node["type"]),
        "part_tag": part_tag,
        "state": "retired" if part_tag == RETIRED_PART_TAG else "current",
    }
    name = node.get("name")
    if name:
        record["name"] = str(name)
    return record


def flatten_part_tree(
    root: Mapping[str, Any], records: dict[str, dict[str, Any]]
) -> int:
    """Merge a part tree into *records* and return raw node occurrences."""

    part_tag = str(root.get("tag", ""))
    if part_tag not in PART_TAGS:
        raise IndexErrorWithContext(f"unexpected part root {part_tag!r}")
    occurrences = 0

    def visit(node: Mapping[str, Any]) -> None:
        nonlocal occurrences
        occurrences += 1
        record = normalize_tree_record(node, part_tag)
        tag = record["tag"]
        previous = records.get(tag)
        if previous is not None and previous != record:
            raise IndexErrorWithContext(
                f"inconsistent duplicate metadata for {tag}: "
                f"{previous!r} != {record!r}"
            )
        records[tag] = record
        children = node.get("children", [])
        if not isinstance(children, list):
            raise IndexErrorWithContext(f"non-list children for {tag}: {children!r}")
        for child in children:
            if not isinstance(child, dict):
                raise IndexErrorWithContext(f"non-object child below {tag}: {child!r}")
            visit(child)

    visit(root)
    return occurrences


def parse_official_total(statistics_html: str) -> int:
    """Read the official total tag count from Kerodon's statistics page."""

    match = TOTAL_PATTERN.search(statistics_html)
    if match is None:
        raise IndexErrorWithContext("could not locate Kerodon's total tag count")
    return int(match.group(1))


def parse_tag_page(tag: str, page: bytes) -> dict[str, Any] | None:
    """Return orphan metadata from a tag page, or ``None`` for an absent tag."""

    text = page.decode("utf-8")
    title_match = TITLE_HTML_PATTERN.search(text)
    if title_match is None:
        raise IndexErrorWithContext(f"tag page {tag} has no title")
    title = html.unescape(title_match.group(1)).strip()
    match = TITLE_PATTERN.fullmatch(title)
    if match is None:
        return None
    metadata = match.groupdict()
    if metadata["tag"] != tag:
        raise IndexErrorWithContext(
            f"tag page mismatch: requested {tag}, received {metadata['tag']}"
        )
    reference = metadata["reference"]
    part_tag = RETIRED_PART_TAG if reference.split(".")[0] == "11" else ""
    if not part_tag:
        raise IndexErrorWithContext(
            f"orphan {tag} at {reference} is not in the retired appendix"
        )
    return {
        "tag": tag,
        "reference": reference,
        "kind": metadata["kind"].lower(),
        "part_tag": part_tag,
        "state": "retired",
        "orphan": True,
    }


def recover_orphans(
    records: dict[str, dict[str, Any]], official_total: int
) -> tuple[list[str], dict[str, str]]:
    """Recover valid tags omitted from every public hierarchy tree."""

    deficit = official_total - len(records)
    if deficit < 0:
        raise IndexErrorWithContext(
            f"part trees contain {len(records)} unique tags, exceeding the "
            f"official total {official_total}"
        )
    if deficit == 0:
        return [], {}

    greatest = max(tag_number(tag) for tag in records)
    gaps = [
        tag_from_number(number)
        for number in range(greatest + 1)
        if tag_from_number(number) not in records
    ]
    recovered: list[str] = []
    response_digests: dict[str, str] = {}
    for tag in gaps:
        statement = fetch_bytes(f"/data/tag/{tag}/content/statement")
        if statement.strip() in {
            b"This tag does not exist.",
            b"This is not a valid tag.",
        }:
            continue
        page = fetch_bytes(f"/tag/{tag}")
        metadata = parse_tag_page(tag, page)
        if metadata is None:
            raise IndexErrorWithContext(
                f"statement API recognizes {tag}, but its tag-page title is malformed"
            )
        records[tag] = metadata
        recovered.append(tag)
        response_digests[f"/tag/{tag}"] = sha256(page)
        if len(recovered) == deficit:
            break

    if len(recovered) != deficit:
        raise IndexErrorWithContext(
            f"official total requires {deficit} orphan tags, but allocator-gap "
            f"probing recovered only {len(recovered)}"
        )
    return recovered, response_digests


def reference_key(reference: str) -> tuple[tuple[int, int | str], ...]:
    """Return a natural key for dotted numeric (or future mixed) references."""

    key: list[tuple[int, int | str]] = []
    for component in reference.split("."):
        if component.isdigit():
            key.append((0, int(component)))
        else:
            key.append((1, component))
    return tuple(key)


def record_source_key(record: Mapping[str, Any]) -> tuple[Any, ...]:
    """Order records by printed reference and then stable tag allocation."""

    return (reference_key(str(record["reference"])), tag_number(str(record["tag"])))


def compute_counts(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    """Compute the redundant audit counts stored with the snapshot."""

    all_by_kind = Counter(str(record["kind"]) for record in records)
    units = [record for record in records if record["kind"] not in STRUCTURAL_KINDS]
    units_by_kind = Counter(str(record["kind"]) for record in units)
    tags_by_state = Counter(str(record["state"]) for record in records)
    units_by_state = Counter(str(record["state"]) for record in units)
    return {
        "all_tags": len(records),
        "structural_tags": len(records) - len(units),
        "mathematical_units": len(units),
        "all_tags_by_kind": dict(sorted(all_by_kind.items())),
        "units_by_kind": dict(sorted(units_by_kind.items())),
        "tags_by_state": dict(sorted(tags_by_state.items())),
        "units_by_state": dict(sorted(units_by_state.items())),
    }


def build_snapshot() -> dict[str, Any]:
    """Fetch and normalize a complete Kerodon metadata snapshot."""

    retrieved_at = utc_now()
    statistics = fetch_bytes("/statistics")
    official_total = parse_official_total(statistics.decode("utf-8"))
    response_digests = {"/statistics": sha256(statistics)}
    records: dict[str, dict[str, Any]] = {}
    raw_occurrences = 0
    roots: list[dict[str, str]] = []

    for part_tag in PART_TAGS:
        path = f"/data/tag/{part_tag}/structure"
        payload = fetch_bytes(path)
        response_digests[path] = sha256(payload)
        root = json.loads(payload)
        if not isinstance(root, dict):
            raise IndexErrorWithContext(f"non-object structure response for {part_tag}")
        if root.get("type") != "part" or root.get("tag") != part_tag:
            raise IndexErrorWithContext(f"unexpected structure root for {part_tag}: {root!r}")
        roots.append(
            {
                "tag": part_tag,
                "reference": str(root["reference"]),
                "name": str(root.get("name", "")),
            }
        )
        raw_occurrences += flatten_part_tree(root, records)

    tree_unique_tags = len(records)
    orphan_tags, orphan_digests = recover_orphans(records, official_total)
    response_digests.update(orphan_digests)
    normalized_records = sorted(records.values(), key=lambda record: tag_number(record["tag"]))
    counts = compute_counts(normalized_records)

    snapshot: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "source": {
            "title": "Kerodon",
            "base_url": BASE_URL,
            "retrieved_at": retrieved_at,
            "official_total_tags": official_total,
            "part_roots": roots,
            "tree_raw_occurrences": raw_occurrences,
            "tree_unique_tags": tree_unique_tags,
            "orphan_tags": orphan_tags,
            "response_sha256": dict(sorted(response_digests.items())),
        },
        "counts": counts,
        "records": normalized_records,
    }
    validate_snapshot(snapshot)
    return snapshot


def validate_snapshot(snapshot: Mapping[str, Any]) -> None:
    """Validate completeness, uniqueness, hierarchy, and redundant counts."""

    if snapshot.get("schema_version") != SCHEMA_VERSION:
        raise IndexErrorWithContext(
            f"unsupported snapshot schema {snapshot.get('schema_version')!r}"
        )
    source = snapshot.get("source")
    records_value = snapshot.get("records")
    if not isinstance(source, dict) or not isinstance(records_value, list):
        raise IndexErrorWithContext("snapshot must contain source metadata and records")
    records: list[Mapping[str, Any]] = records_value
    official_total = source.get("official_total_tags")
    if not isinstance(official_total, int) or official_total <= 0:
        raise IndexErrorWithContext("snapshot has no positive official tag total")
    if len(records) != official_total:
        raise IndexErrorWithContext(
            f"snapshot has {len(records)} records, expected {official_total}"
        )

    by_tag: dict[str, Mapping[str, Any]] = {}
    for record in records:
        required = ("tag", "reference", "kind", "part_tag", "state")
        missing = [field for field in required if not record.get(field)]
        if missing:
            raise IndexErrorWithContext(
                f"record missing {', '.join(missing)}: {record!r}"
            )
        tag = str(record["tag"])
        tag_number(tag)
        if tag in by_tag:
            raise IndexErrorWithContext(f"duplicate record for tag {tag}")
        by_tag[tag] = record
        if record["state"] not in {"current", "retired"}:
            raise IndexErrorWithContext(f"invalid state for {tag}: {record['state']!r}")
        if record["part_tag"] not in PART_TAGS:
            raise IndexErrorWithContext(
                f"invalid part root for {tag}: {record['part_tag']!r}"
            )
        expected_state = (
            "retired" if record["part_tag"] == RETIRED_PART_TAG else "current"
        )
        if record["state"] != expected_state:
            raise IndexErrorWithContext(
                f"state/part mismatch for {tag}: {record['state']} vs "
                f"{record['part_tag']}"
            )

    chapters = {
        str(record["reference"]): record
        for record in records
        if record["kind"] == "chapter"
    }
    for record in records:
        if record["kind"] in {"part", "chapter"}:
            continue
        chapter_reference = str(record["reference"]).split(".")[0]
        if chapter_reference not in chapters:
            raise IndexErrorWithContext(
                f"tag {record['tag']} has no chapter at {chapter_reference}"
            )

    computed = compute_counts(records)
    if snapshot.get("counts") != computed:
        raise IndexErrorWithContext(
            f"stored counts disagree with records: {snapshot.get('counts')!r} "
            f"!= {computed!r}"
        )
    if computed["structural_tags"] + computed["mathematical_units"] != official_total:
        raise IndexErrorWithContext("structural and unit counts do not exhaust all tags")

    orphan_tags = source.get("orphan_tags")
    if not isinstance(orphan_tags, list):
        raise IndexErrorWithContext("source.orphan_tags must be a list")
    for tag in orphan_tags:
        record = by_tag.get(str(tag))
        if record is None or record.get("orphan") is not True:
            raise IndexErrorWithContext(f"orphan audit mismatch for {tag}")


def markdown_escape(value: str) -> str:
    """Escape table delimiters and collapse source whitespace."""

    return " ".join(value.split()).replace("|", "\\|")


def title_case_kind(kind: str) -> str:
    """Render a source kind without changing its mathematical content."""

    return kind[:1].upper() + kind[1:]


def heading_maps(
    records: Sequence[Mapping[str, Any]],
) -> dict[str, dict[str, Mapping[str, Any]]]:
    """Index structural records by kind and printed reference."""

    result: dict[str, dict[str, Mapping[str, Any]]] = {
        kind: {} for kind in STRUCTURAL_KINDS
    }
    for record in records:
        kind = str(record["kind"])
        if kind not in STRUCTURAL_KINDS:
            continue
        reference = str(record["reference"])
        previous = result[kind].get(reference)
        if previous is not None:
            raise IndexErrorWithContext(
                f"multiple {kind} records at reference {reference}"
            )
        result[kind][reference] = record
    return result


def location_for(
    record: Mapping[str, Any], headings: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> str:
    """Return named section/subsection context for one mathematical unit."""

    components = str(record["reference"]).split(".")
    pieces: list[str] = []
    for depth, kind in ((2, "section"), (3, "subsection"), (4, "subsubsection")):
        if len(components) < depth:
            continue
        reference = ".".join(components[:depth])
        heading = headings[kind].get(reference)
        if heading is None:
            continue
        name = str(heading.get("name", "")).strip()
        label = f"§{reference}"
        if name:
            label += f" {name}"
        pieces.append(label)
    return " › ".join(pieces) if pieces else "Chapter introduction"


def render_markdown(snapshot: Mapping[str, Any]) -> str:
    """Render the human-browsable exhaustive catalogue."""

    validate_snapshot(snapshot)
    source = snapshot["source"]
    counts = snapshot["counts"]
    records: list[Mapping[str, Any]] = snapshot["records"]
    headings = heading_maps(records)
    units = [record for record in records if record["kind"] not in STRUCTURAL_KINDS]
    chapters = sorted(headings["chapter"].values(), key=record_source_key)
    timestamp = str(source["retrieved_at"])

    lines = [
        "---",
        "type: reference",
        "title: Kerodon source-unit index",
        "description: '# Kerodon source-unit index'",
        "tags:",
        "- project",
        "- reference",
        f"timestamp: {timestamp}",
        "scope: project",
        "source: agent",
        "confidence: high",
        "promotable: false",
        "project_id: github.com__dzackgarza__lean-categories",
        "---",
        "",
        "<!-- Generated by scripts/index_kerodon.py; do not edit by hand. -->",
        "",
        "# Kerodon source-unit index",
        "",
        "Source: Jacob Lurie, *Kerodon*, <https://kerodon.net>.",
        "",
        f"Pinned metadata snapshot: `{timestamp}`; normalized source: "
        "`corpus/kerodon-source-units.json`.",
        "",
        "This supplementary catalogue inventories every stable Kerodon tag in the "
        "snapshot. It does not amend the frozen FC01–FC16 foundational-corpus "
        "denominator. Statement and proof prose remain at Kerodon; this repository "
        "stores stable tags, kinds, printed references, explicit names, hierarchy, "
        "and current/retired state.",
        "",
        "## Completeness contract",
        "",
        f"- Kerodon's statistics endpoint reported **{counts['all_tags']:,} tags**.",
        f"- The snapshot contains exactly **{counts['all_tags']:,} unique tags**: "
        f"**{counts['structural_tags']:,} structural tags** and "
        f"**{counts['mathematical_units']:,} mathematical units**.",
        f"- Mathematical units comprise **{counts['units_by_state']['current']:,} "
        f"current** and **{counts['units_by_state']['retired']:,} retired** records.",
        "- Definitions, constructions, notation, theorem-like results, examples, "
        "remarks, exercises, questions, warnings, variants, equations, and equation "
        "arrays are all included; no non-structural kind is filtered.",
        f"- The hierarchy trees omitted {len(source['orphan_tags'])} valid retired "
        "tags. They were recovered by reconciling allocator gaps against the "
        "official total: "
        + ", ".join(f"`{tag}`" for tag in source["orphan_tags"])
        + ".",
        "- `python scripts/index_kerodon.py --check` validates the checked-in "
        "snapshot and generated catalogue without network access. "
        "`python scripts/index_kerodon.py --refresh` refreshes both from Kerodon.",
        "",
        "## Unit counts",
        "",
        "| Kind | Current | Retired | Total |",
        "| --- | ---: | ---: | ---: |",
    ]

    for kind, total in counts["units_by_kind"].items():
        current = sum(
            1
            for record in units
            if record["kind"] == kind and record["state"] == "current"
        )
        retired = total - current
        lines.append(
            f"| {title_case_kind(kind)} | {current:,} | {retired:,} | {total:,} |"
        )
    lines.extend(
        [
            f"| **Total** | **{counts['units_by_state']['current']:,}** | "
            f"**{counts['units_by_state']['retired']:,}** | "
            f"**{counts['mathematical_units']:,}** |",
            "",
            "## Stable-tag catalogue",
            "",
            "`KER-XXXX` is a repository-local source-unit ID whose suffix is "
            "Kerodon's permanent tag. The ID links to the authoritative source item.",
            "",
        ]
    )

    for chapter in chapters:
        chapter_reference = str(chapter["reference"])
        chapter_name = markdown_escape(str(chapter.get("name", "")))
        chapter_state = str(chapter["state"])
        chapter_units = sorted(
            [
                record
                for record in units
                if str(record["reference"]).split(".")[0] == chapter_reference
            ],
            key=record_source_key,
        )
        status_suffix = " (retired stable tags)" if chapter_state == "retired" else ""
        lines.extend(
            [
                f"## Chapter {chapter_reference}. {chapter_name}{status_suffix}",
                "",
                f"Units: **{len(chapter_units):,}**.",
                "",
                "| ID | Reference | Kind | Explicit name | Section context |",
                "| --- | --- | --- | --- | --- |",
            ]
        )
        for record in chapter_units:
            tag = str(record["tag"])
            name = markdown_escape(str(record.get("name", "—")))
            context = markdown_escape(location_for(record, headings))
            lines.append(
                f"| [KER-{tag}]({BASE_URL}/tag/{tag}) | "
                f"{markdown_escape(str(record['reference']))} | "
                f"{title_case_kind(str(record['kind']))} | {name} | {context} |"
            )
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def atomic_write(path: Path, data: str) -> None:
    """Write UTF-8 text atomically in the destination directory."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(data)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def load_snapshot(path: Path) -> dict[str, Any]:
    """Load and validate a normalized snapshot."""

    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise IndexErrorWithContext(f"snapshot does not exist: {path}") from error
    if not isinstance(value, dict):
        raise IndexErrorWithContext(f"snapshot root is not an object: {path}")
    validate_snapshot(value)
    return value


def serialized_snapshot(snapshot: Mapping[str, Any]) -> str:
    """Serialize the canonical normalized snapshot."""

    return json.dumps(snapshot, ensure_ascii=False, indent=2, sort_keys=False) + "\n"


def check_file(path: Path, expected: str) -> None:
    """Require *path* to match generated content exactly."""

    try:
        actual = path.read_text(encoding="utf-8")
    except FileNotFoundError as error:
        raise IndexErrorWithContext(f"generated file does not exist: {path}") from error
    if actual != expected:
        raise IndexErrorWithContext(
            f"generated file is stale: {path}; run "
            "python scripts/index_kerodon.py"
        )


def parse_arguments(argv: Sequence[str]) -> argparse.Namespace:
    """Parse command-line arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT_SNAPSHOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--refresh",
        action="store_true",
        help="fetch a new official snapshot, then write snapshot and catalogue",
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="validate the snapshot and require the catalogue to be current",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""

    arguments = parse_arguments(sys.argv[1:] if argv is None else argv)
    try:
        if arguments.refresh:
            snapshot = build_snapshot()
            atomic_write(arguments.snapshot, serialized_snapshot(snapshot))
        else:
            snapshot = load_snapshot(arguments.snapshot)
        rendered = render_markdown(snapshot)
        if arguments.check:
            check_file(arguments.output, rendered)
        else:
            atomic_write(arguments.output, rendered)
    except (IndexErrorWithContext, json.JSONDecodeError) as error:
        print(f"Kerodon index error: {error}", file=sys.stderr)
        return 1

    counts = snapshot["counts"]
    action = "verified" if arguments.check else "wrote"
    print(
        f"{action} {counts['mathematical_units']} Kerodon mathematical units "
        f"from {counts['all_tags']} stable tags"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
