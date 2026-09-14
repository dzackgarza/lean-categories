#!/usr/bin/env python3
"""Search the live Formalization Corpus API from repository workflows.

The hosted API is a mandatory Sweep-II discovery surface, not a fallback after
local searches.  The public OpenAPI document is the only endpoint/method
authority for this client:

    https://formalization-corpus.dzackgarza.com/api/openapi.json

The client resolves operations by their OpenAPI ``operationId`` on every run;
paths and HTTP methods are deliberately not duplicated here.  Users who prefer
a generated client should use the client-generation examples exposed by the
Formalization Corpus API reference itself.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import sys
import urllib.error
import urllib.request
from typing import Any, Mapping, Sequence


DEFAULT_OPENAPI_URL = "https://formalization-corpus.dzackgarza.com/api/openapi.json"
OPENAPI_URL = os.environ.get("FORMALIZATION_CORPUS_OPENAPI", DEFAULT_OPENAPI_URL)
USER_AGENT = (
    "lean-categories formalization-corpus client/1 "
    "(https://github.com/dzackgarza/lean-categories)"
)


class CorpusAPIError(RuntimeError):
    """A failed or malformed Formalization Corpus API request."""


def load_openapi() -> dict[str, Any]:
    """Load the authoritative live API contract."""

    request = urllib.request.Request(
        OPENAPI_URL,
        headers={"Accept": "application/json", "User-Agent": USER_AGENT},
    )
    try:
        with urllib.request.urlopen(request, timeout=120) as response:
            value = json.load(response)
    except urllib.error.HTTPError as error:
        detail = error.read().decode("utf-8", "replace")
        raise CorpusAPIError(
            f"{request.full_url} returned HTTP {error.code}: {detail}"
        ) from error
    except (TimeoutError, urllib.error.URLError) as error:
        raise CorpusAPIError(f"failed to reach {request.full_url}: {error}") from error
    except json.JSONDecodeError as error:
        raise CorpusAPIError(f"non-JSON OpenAPI response from {request.full_url}") from error
    if not isinstance(value, dict):
        raise CorpusAPIError(f"non-object OpenAPI response from {request.full_url}")
    return value


def resolve_operation(spec: Mapping[str, Any], operation_id: str) -> tuple[str, str]:
    """Resolve one operation ID to its absolute URL and HTTP method."""

    servers = spec.get("servers")
    if not isinstance(servers, list) or not servers or not isinstance(servers[0], dict):
        raise CorpusAPIError("OpenAPI document has no usable server URL")
    base_url = servers[0].get("url")
    if not isinstance(base_url, str) or not base_url:
        raise CorpusAPIError("OpenAPI document has no usable server URL")

    paths = spec.get("paths")
    if not isinstance(paths, dict):
        raise CorpusAPIError("OpenAPI document has no paths object")
    matches: list[tuple[str, str]] = []
    for path, methods in paths.items():
        if not isinstance(path, str) or not isinstance(methods, dict):
            continue
        for method, operation in methods.items():
            if not isinstance(operation, dict):
                continue
            if operation.get("operationId") == operation_id:
                matches.append((str(method).upper(), path))
    if len(matches) != 1:
        raise CorpusAPIError(
            f"OpenAPI operationId {operation_id!r} resolved to {len(matches)} operations"
        )
    method, path = matches[0]
    return base_url.rstrip("/") + path, method


def call_operation(
    spec: Mapping[str, Any], operation_id: str, payload: Mapping[str, Any]
) -> dict[str, Any]:
    """Invoke an operation resolved solely from the OpenAPI document."""

    body = json.dumps(payload).encode("utf-8")
    url, method = resolve_operation(spec, operation_id)
    request = urllib.request.Request(
        url,
        data=body,
        method=method,
        headers={
            "Accept": "application/json",
            "Content-Type": "application/json",
            "User-Agent": USER_AGENT,
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=120) as response:
            value = json.load(response)
    except urllib.error.HTTPError as error:
        detail = error.read().decode("utf-8", "replace")
        raise CorpusAPIError(
            f"{request.full_url} returned HTTP {error.code}: {detail}"
        ) from error
    except (TimeoutError, urllib.error.URLError) as error:
        raise CorpusAPIError(f"failed to reach {request.full_url}: {error}") from error
    except json.JSONDecodeError as error:
        raise CorpusAPIError(f"non-JSON response from {request.full_url}") from error
    if not isinstance(value, dict):
        raise CorpusAPIError(f"non-object response from {request.full_url}")
    return value


def decode_content(value: object) -> str:
    """Decode an API base64 content field, tolerating an absent field."""

    if not isinstance(value, str) or not value:
        return ""
    try:
        return base64.b64decode(value, validate=True).decode("utf-8", "replace")
    except (ValueError, UnicodeDecodeError) as error:
        raise CorpusAPIError("malformed base64 content in search result") from error


def search_payload(arguments: argparse.Namespace) -> dict[str, Any]:
    """Build the OpenAPI SearchRequest payload."""

    options: dict[str, Any] = {
        "MaxDocDisplayCount": arguments.max_files,
        "MaxMatchDisplayCount": arguments.max_matches,
        "ChunkMatches": True,
        "NumContextLines": arguments.context,
    }
    if arguments.whole:
        options["Whole"] = True
    return {"Q": arguments.query, "Opts": options}


def print_search(response: Mapping[str, Any], *, whole: bool) -> None:
    """Render search results with decoded source snippets."""

    result = response.get("Result")
    if not isinstance(result, dict):
        raise CorpusAPIError("search response has no Result object")
    files = result.get("Files", [])
    if not isinstance(files, list):
        raise CorpusAPIError("search Result.Files is not a list")

    print(
        "files="
        f"{result.get('FileCount', len(files))} "
        f"matches={result.get('MatchCount', '?')} "
        f"returned={len(files)}"
    )
    for index, file_match in enumerate(files, start=1):
        if not isinstance(file_match, dict):
            raise CorpusAPIError("search result contains a non-object file match")
        repository = file_match.get("Repository", "?")
        filename = file_match.get("FileName", "?")
        language = file_match.get("Language") or "?"
        role = file_match.get("FileRole") or "?"
        print(f"\n[{index}] {repository}\t{filename}\t{language}\t{role}")

        chunks = file_match.get("ChunkMatches") or []
        if not isinstance(chunks, list):
            raise CorpusAPIError("FileMatch.ChunkMatches is not a list")
        for chunk in chunks:
            if not isinstance(chunk, dict):
                raise CorpusAPIError("ChunkMatches contains a non-object entry")
            text = decode_content(chunk.get("Content"))
            if text:
                print(text.rstrip())

        if whole:
            content = decode_content(file_match.get("Content"))
            if content:
                print("\n--- complete file ---")
                print(content.rstrip())


def print_list(response: Mapping[str, Any]) -> None:
    """Render repository names and live index metadata."""

    listing = response.get("List")
    if not isinstance(listing, dict):
        raise CorpusAPIError("list response has no List object")
    repositories = listing.get("Repos") or []
    if not isinstance(repositories, list):
        raise CorpusAPIError("List.Repos is not a list")
    for entry in repositories:
        if not isinstance(entry, dict):
            raise CorpusAPIError("List.Repos contains a non-object entry")
        repository = entry.get("Repository")
        if not isinstance(repository, dict):
            raise CorpusAPIError("repository entry has no Repository object")
        stats = entry.get("Stats") if isinstance(entry.get("Stats"), dict) else {}
        metadata = (
            entry.get("IndexMetadata")
            if isinstance(entry.get("IndexMetadata"), dict)
            else {}
        )
        print(
            f"{repository.get('Name', '?')}\t"
            f"documents={stats.get('Documents', '?')}\t"
            f"indexed={metadata.get('IndexTime', '?')}"
        )


def parse_arguments(argv: Sequence[str]) -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit the API response verbatim instead of decoded human output",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    search = subparsers.add_parser("search", help="run OpenAPI operation searchCorpus")
    search.add_argument("query", help="Zoekt query; bare terms search all repositories")
    search.add_argument("--max-files", type=int, default=20)
    search.add_argument("--max-matches", type=int, default=200)
    search.add_argument("--context", type=int, default=2)
    search.add_argument(
        "--whole",
        action="store_true",
        help="request and decode each complete matching file",
    )

    listing = subparsers.add_parser("list", help="run OpenAPI operation listSources")
    listing.add_argument(
        "query",
        nargs="?",
        default="",
        help="repository query, e.g. repo:mathlib4; empty lists all sources",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""

    arguments = parse_arguments(sys.argv[1:] if argv is None else argv)
    try:
        spec = load_openapi()
        if arguments.command == "search":
            response = call_operation(spec, "searchCorpus", search_payload(arguments))
        elif arguments.command == "list":
            response = call_operation(spec, "listSources", {"Q": arguments.query})
        else:  # argparse makes this unreachable.
            raise CorpusAPIError(f"unsupported command {arguments.command!r}")

        if arguments.json:
            json.dump(response, sys.stdout, ensure_ascii=False, indent=2)
            print()
        elif arguments.command == "search":
            print_search(response, whole=arguments.whole)
        else:
            print_list(response)
    except CorpusAPIError as error:
        print(f"formalization-corpus API error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
