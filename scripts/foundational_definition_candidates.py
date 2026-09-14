#!/usr/bin/env python3
"""Bulk-discover formalization candidates for unresolved corpus definitions.

The input is the generated ``FOUNDATIONAL_DEFINITIONS.tsv`` table.  This tool
does not accept mappings: it performs the cheap corpus-wide discovery pass and
writes a candidate table for semantic inspection.  Canonical mapping decisions
remain in ``corpus/``.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import html.parser
import json
import re
import urllib.request
from pathlib import Path
from typing import Any, Mapping

import formalization_corpus as api


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = REPOSITORY_ROOT / "FOUNDATIONAL_DEFINITIONS.tsv"
DEFAULT_OUTPUT = REPOSITORY_ROOT / ".tmp" / "foundational-definition-candidates.tsv"
DEFAULT_KERODON_CACHE = REPOSITORY_ROOT / ".tmp" / "kerodon-definition-query-cache.json"
KERODON_TAG_ALPHABET = "0123456789ABCDEFGHJKLMNPQRSTUVWXYZ"

STOPWORDS = {
    "a",
    "an",
    "and",
    "as",
    "at",
    "by",
    "construction",
    "convention",
    "definition",
    "definitions",
    "for",
    "from",
    "in",
    "notation",
    "of",
    "on",
    "or",
    "the",
    "to",
    "via",
    "with",
}


class KerodonStatementParser(html.parser.HTMLParser):
    """Extract short mathematical terminology and plain text from a statement."""

    def __init__(self) -> None:
        super().__init__()
        self.em_depth = 0
        self.em_buffer: list[str] = []
        self.terms: list[str] = []
        self.text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "em":
            self.em_depth += 1
            self.em_buffer = []

    def handle_data(self, data: str) -> None:
        self.text.append(data)
        if self.em_depth:
            self.em_buffer.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag == "em" and self.em_depth:
            term = " ".join("".join(self.em_buffer).split())
            if term and term.casefold() != "the":
                self.terms.append(term)
            self.em_depth -= 1
            self.em_buffer = []


def kerodon_tag_from_unit_id(unit_id: str) -> str:
    """Invert FC17's one-based ambiguity-free tag allocator ordinal."""

    match = re.fullmatch(r"FC17-KER-U(\d{5})", unit_id)
    if match is None:
        raise ValueError(f"not an FC17 Kerodon unit ID: {unit_id}")
    value = int(match.group(1)) - 1
    chars: list[str] = []
    for _ in range(4):
        value, remainder = divmod(value, len(KERODON_TAG_ALPHABET))
        chars.append(KERODON_TAG_ALPHABET[remainder])
    if value:
        raise ValueError(f"Kerodon ordinal does not fit four characters: {unit_id}")
    return "".join(reversed(chars))


def fetch_kerodon_query_data(tag: str) -> dict[str, Any]:
    """Fetch one Kerodon statement and retain only discovery-oriented data."""

    request = urllib.request.Request(
        f"https://kerodon.net/data/tag/{tag}/content/statement",
        headers={"User-Agent": "lean-categories Kerodon mapping/1"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        source = response.read().decode("utf-8")
    parser = KerodonStatementParser()
    parser.feed(source)
    plain = " ".join(" ".join(parser.text).split())
    plain = re.sub(
        r"^(?:Definition|Construction|Notation|Convention)\s+[0-9.]+\s*\.\s*",
        "",
        plain,
        flags=re.IGNORECASE,
    )
    # This cache is scratch retrieval input, not another copy of the source:
    # retain only a short lead for the minority of units with no emphasized term.
    return {"terms": list(dict.fromkeys(parser.terms)), "lead": plain[:360]}


def kerodon_query_cache(
    rows: list[Mapping[str, str]], cache_path: Path, *, workers: int = 12
) -> dict[str, dict[str, Any]]:
    """Populate a resumable scratch cache for selected FC17 source statements."""

    if cache_path.exists():
        value = json.loads(cache_path.read_text(encoding="utf-8"))
        cache = value if isinstance(value, dict) else {}
    else:
        cache = {}
    tags = [
        kerodon_tag_from_unit_id(row["unit_id"])
        for row in rows
        if row["source_id"] == "FC17"
    ]
    missing = [tag for tag in dict.fromkeys(tags) if tag not in cache]
    if missing:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            futures = {executor.submit(fetch_kerodon_query_data, tag): tag for tag in missing}
            for future in concurrent.futures.as_completed(futures):
                tag = futures[future]
                cache[tag] = future.result()
        cache_path.write_text(
            json.dumps(cache, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    return cache


def enrich_kerodon_rows(
    rows: list[dict[str, str]], cache: Mapping[str, Mapping[str, Any]]
) -> None:
    """Replace tag-only FC17 search keys with source-defined terminology."""

    for row in rows:
        if row["source_id"] != "FC17":
            continue
        # Kerodon's explicit environment name is already source-authored
        # terminology and is normally a better retrieval key than incidental
        # emphasized words in the body.
        if not re.fullmatch(r"Kerodon\s+[0-9A-Z]{4}", row["search_key"].strip()):
            continue
        tag = kerodon_tag_from_unit_id(row["unit_id"])
        data = cache.get(tag, {})
        terms_value = data.get("terms") if isinstance(data, Mapping) else None
        terms = [str(term) for term in terms_value] if isinstance(terms_value, list) else []
        if terms:
            semantic = " ".join(terms[:3])
            # A short term such as "strictly increasing" or "face operator"
            # is ambiguous across mathematics.  Kerodon's section title is a
            # cheap source-authored disambiguator (e.g. "Simplicial Sets").
            plain_words = re.findall(r"[A-Za-z]+", semantic)
            context_match = re.search(r"§[^;]+?\s+([^;]+)$", row["source_location"])
            if len(plain_words) <= 4 and context_match is not None:
                context_words = [
                    word
                    for word in re.findall(r"[A-Za-z]+", context_match.group(1))
                    if word.casefold() not in STOPWORDS
                ][:2]
                existing_words = {word.casefold() for word in plain_words}
                extras = [word for word in context_words if word.casefold() not in existing_words]
                if extras:
                    semantic += " " + " ".join(extras)
            row["search_key"] = semantic
            continue
        lead = data.get("lead") if isinstance(data, Mapping) else None
        if isinstance(lead, str) and lead.strip():
            row["search_key"] = lead.strip()


def query_for(row: Mapping[str, str]) -> str:
    """Turn a source-facing label into a broad first-pass Zoekt query."""

    raw = row["search_key"].strip()
    direct_tag = re.fullmatch(r"Kerodon\s+([0-9A-Z]{4})", raw)
    if direct_tag is not None:
        return f"kerodon {direct_tag.group(1)}"

    text = raw.replace("∞", "infinity")
    text = re.sub(r"\\(?:text|operatorname|mathrm|mathbf|mathbb|mathcal)\s*", " ", text)
    text = re.sub(r"[^0-9A-Za-z_+*-]+", " ", text)
    words = [
        word
        for word in text.split()
        if len(word) >= 2 and word.lower() not in STOPWORDS
    ]
    # Preserve enough of a compound mathematical name to disambiguate it, but
    # avoid requiring incidental prose words to occur in the same source file.
    return " ".join(words[:8]) or raw


def mapping_hint_key(hint: str) -> str:
    """Extract the mathematical target from a prior negative mapping summary."""

    value = hint.strip()
    if not value or value.lower().startswith("unmatched source theorem/construction"):
        return ""
    # Negative summaries conventionally put the object being sought immediately
    # before “remains unmatched”.  When a sentence contrasts existing ingredients
    # with the missing owner, prefer the clause after “but”.
    match = re.search(r"\bbut\s+(?:the\s+)?(.+?)\s+remains?\s+unmatched\b", value, re.I)
    if match is not None:
        return match.group(1).strip(" ;,.")
    value = re.split(r"\s+remains?\s+unmatched\b", value, maxsplit=1, flags=re.I)[0]
    return value.strip(" ;,.")


def candidate_summary(response: Mapping[str, Any]) -> tuple[str, str, str]:
    """Return file/match counts and a compact list of top source locations."""

    result = response.get("Result")
    if not isinstance(result, dict):
        raise api.CorpusAPIError("candidate search response has no Result object")
    files = result.get("Files") or []
    if not isinstance(files, list):
        raise api.CorpusAPIError("candidate search Result.Files is not a list")
    candidates: list[str] = []
    for hit in files[:8]:
        if not isinstance(hit, dict):
            continue
        repository = str(hit.get("Repository", "?"))
        filename = str(hit.get("FileName", "?"))
        role = str(hit.get("FileRole") or "")
        suffix = f" [{role}]" if role else ""
        candidates.append(f"{repository}::{filename}{suffix}")
    return (
        str(result.get("FileCount", len(files))),
        str(result.get("MatchCount", "?")),
        "; ".join(candidates),
    )


def chunks[T](values: list[T], size: int) -> list[list[T]]:
    """Split a list into nonempty consecutive chunks."""

    return [values[index : index + size] for index in range(0, len(values), size)]


def batch_payload(rows: list[Mapping[str, str]], *, concurrency: int) -> dict[str, Any]:
    """Build one OpenAPI batch request for unresolved definition rows."""

    searches: list[dict[str, Any]] = []
    for row in rows:
        query = query_for(row)
        searches.append(
            {
                "ID": row["unit_id"],
                "Request": {
                    "Q": query,
                    "Opts": {
                        "MaxDocDisplayCount": 8,
                        # The census only needs candidate source locations.  Do
                        # not pay to serialize matching source chunks until a
                        # candidate is selected for semantic verification.
                        "MaxMatchDisplayCount": 8,
                        "ChunkMatches": False,
                        "NumContextLines": 0,
                        "MaxWallTime": 2_000_000_000,
                    },
                },
            }
        )
    return {"Searches": searches, "MaxConcurrency": concurrency}


def consume_batch(
    response: Mapping[str, Any],
    rows_by_id: Mapping[str, Mapping[str, str]],
) -> tuple[list[list[str]], list[tuple[str, str]]]:
    """Normalize a batch API response into candidate rows and failures."""

    results = response.get("Results")
    if not isinstance(results, list):
        raise api.CorpusAPIError("batch candidate response has no Results list")
    accepted: list[list[str]] = []
    failures: list[tuple[str, str]] = []
    for item in results:
        if not isinstance(item, dict):
            raise api.CorpusAPIError("batch candidate Results contains a non-object entry")
        unit_id = item.get("ID")
        if not isinstance(unit_id, str) or unit_id not in rows_by_id:
            raise api.CorpusAPIError(f"batch candidate response has unknown ID {unit_id!r}")
        row = rows_by_id[unit_id]
        query = query_for(row)
        if item.get("StatusCode") != 200 or not isinstance(item.get("Result"), dict):
            failures.append((unit_id, str(item.get("Error") or "search failed")))
            continue
        files, matches, candidates = candidate_summary({"Result": item["Result"]})
        accepted.append(
            [
                unit_id,
                row["source_id"],
                row["label"],
                query,
                files,
                matches,
                candidates,
            ]
        )
    return accepted, failures


def read_existing(path: Path) -> dict[str, list[str]]:
    """Read a prior candidate table for resumable bulk searches."""

    if not path.exists():
        return {}
    with path.open(encoding="utf-8", newline="") as handle:
        return {
            row["unit_id"]: [
                row["unit_id"],
                row["source_id"],
                row["label"],
                row["query"],
                row["file_count"],
                row["match_count"],
                row["candidates"],
            ]
            for row in csv.DictReader(handle, dialect="excel-tab")
        }


def write_candidates(
    path: Path,
    existing: Mapping[str, list[str]],
    order: Mapping[str, int],
) -> None:
    """Checkpoint the accumulated candidate census deterministically."""

    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, dialect="excel-tab", lineterminator="\n")
        writer.writerow(
            [
                "unit_id",
                "source_id",
                "label",
                "query",
                "file_count",
                "match_count",
                "candidates",
            ]
        )
        for unit_id in sorted(existing, key=lambda value: order.get(value, 10**9)):
            writer.writerow(existing[unit_id])


def search_group(
    spec: Mapping[str, Any],
    group: list[Mapping[str, str]],
    rows_by_id: Mapping[str, Mapping[str, str]],
    *,
    concurrency: int,
) -> tuple[list[list[str]], list[tuple[str, str]]]:
    """Search one batch, recursively splitting transport-level failures."""

    try:
        response = api.call_operation(
            spec,
            "searchCorpusBatch",
            batch_payload(group, concurrency=min(concurrency, len(group))),
            timeout=180,
        )
        return consume_batch(response, rows_by_id)
    except Exception as error:
        if len(group) == 1:
            return [], [(group[0]["unit_id"], str(error))]
        midpoint = len(group) // 2
        left_rows, left_failures = search_group(
            spec,
            group[:midpoint],
            rows_by_id,
            concurrency=concurrency,
        )
        right_rows, right_failures = search_group(
            spec,
            group[midpoint:],
            rows_by_id,
            concurrency=concurrency,
        )
        return left_rows + right_rows, left_failures + right_failures


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--source", action="append", help="limit to one or more FCxx sources")
    parser.add_argument("--limit", type=int, default=0, help="maximum new searches; 0 means all")
    # Keep one public request comfortably below the reverse proxy's origin
    # deadline even when all searches are cold.  Larger corpus scans remain
    # bulk operations: they are simply split into resumable API batches.
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--concurrency", type=int, default=4)
    parser.add_argument("--kerodon-cache", type=Path, default=DEFAULT_KERODON_CACHE)
    parser.add_argument(
        "--query-mode",
        choices=("primary", "mapping-hint"),
        default="primary",
        help="use source-derived search keys or the prior mapping summary as a second formulation",
    )
    parser.add_argument("--no-resume", action="store_true")
    args = parser.parse_args()

    with args.input.open(encoding="utf-8", newline="") as handle:
        all_rows = list(csv.DictReader(handle, dialect="excel-tab"))
    selected = [
        dict(row)
        for row in all_rows
        if row["action"] == "search"
        and (not args.source or row["source_id"] in set(args.source))
    ]
    cache = kerodon_query_cache(selected, args.kerodon_cache)
    enrich_kerodon_rows(selected, cache)
    if args.query_mode == "mapping-hint":
        for row in selected:
            hint = mapping_hint_key(row.get("mapping_hint", ""))
            if hint:
                row["search_key"] = hint

    existing = {} if args.no_resume else read_existing(args.output)
    pending = [row for row in selected if row["unit_id"] not in existing]
    if args.limit > 0:
        pending = pending[: args.limit]

    if not 1 <= args.batch_size <= 512:
        parser.error("--batch-size must be between 1 and 512")
    if not 1 <= args.concurrency <= 32:
        parser.error("--concurrency must be between 1 and 32")

    spec = api.load_openapi()
    failures: list[tuple[str, str]] = []
    rows_by_id = {row["unit_id"]: row for row in pending}
    order = {row["unit_id"]: index for index, row in enumerate(all_rows)}
    groups = chunks(pending, args.batch_size)
    for batch_number, group in enumerate(groups, start=1):
        accepted, group_failures = search_group(
            spec,
            group,
            rows_by_id,
            concurrency=args.concurrency,
        )
        failures.extend(group_failures)
        for candidate in accepted:
            existing[candidate[0]] = candidate
        write_candidates(args.output, existing, order)
        print(
            f"batch {batch_number}/{len(groups)}: +{len(accepted)} searched, "
            f"{len(group_failures)} failures; checkpoint={len(existing)}",
            flush=True,
        )

    # Also create a header-only table when there was no pending work and no
    # existing checkpoint.
    write_candidates(args.output, existing, order)

    positive = sum(int(row[4]) > 0 for row in existing.values() if row[4].isdigit())
    print(
        f"candidate census: {len(existing)} searched, {positive} with hits, "
        f"{len(failures)} request failures"
    )
    for unit_id, error in failures[:20]:
        print(f"FAILED {unit_id}: {error}")


if __name__ == "__main__":
    main()
