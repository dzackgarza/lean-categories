#!/usr/bin/env python3
"""Independent review of a pull request to lean-categories (scripts/review/prompt.md).

Runs in `.github/workflows/independent-review.yml` on `pull_request_target`: this code is main's,
and the pull request's head is only read as data, never run. One model call with no tools, no
settings and no MCP servers; its only input is main's rules and the pull request's diff, never the
author's description. Exit 0 only on approval.

    review.py --base <main checkout> --head <head checkout> --out <dir>
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

MODEL = "claude-opus-5-5"
DIFF_LIMIT = 300_000
CRITERIA = 5
SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string", "enum": ["approve", "reject"]},
        "criteria": {"type": "array", "items": {
            "type": "object",
            "properties": {"criterion": {"type": "string"}, "holds": {"type": "boolean"},
                           "evidence": {"type": "string"}},
            "required": ["criterion", "holds", "evidence"], "additionalProperties": False}},
        "summary": {"type": "string"},
    },
    "required": ["verdict", "criteria", "summary"],
    "additionalProperties": False,
}


def diff(base: Path, head: Path) -> str:
    """The pull request's change: every tracked file of either side, compared."""
    r = subprocess.run(["git", "diff", "--no-index", "--no-color", "--", str(base), str(head)],
                       capture_output=True, text=True)
    if r.returncode not in (0, 1):
        raise SystemExit(f"git diff failed: {r.stderr}")
    return r.stdout.replace(str(base) + "/", "a/").replace(str(head) + "/", "b/")


def review(prompt: Path, rules: str, change: str) -> tuple[dict | None, str]:
    r = subprocess.run(
        ["claude", "-p", "--model", MODEL, "--effort", "high", "--tools", "", "--setting-sources", "",
         "--strict-mcp-config", "--no-session-persistence", "--system-prompt-file", str(prompt),
         "--json-schema", json.dumps(SCHEMA), "--output-format", "json"],
        input="<rules>\n" + rules + "\n</rules>\n\n<untrusted_change>\n" + change
              + "\n</untrusted_change>\n",
        capture_output=True, text=True)
    if r.returncode != 0:
        return None, f"reviewer call failed ({r.returncode}): {(r.stderr or r.stdout).strip()[-500:]}"
    out = json.loads(r.stdout)
    if out.get("is_error") or out.get("subtype") != "success" or "structured_output" not in out:
        return None, f"reviewer stopped: {out.get('subtype')}: {str(out.get('result'))[:500]}"
    return out["structured_output"], ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--base", type=Path, required=True)
    ap.add_argument("--head", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    base, head = a.base.resolve(), a.head.resolve()
    a.out.mkdir(parents=True, exist_ok=True)
    for side in (base, head):
        subprocess.run(["rm", "-rf", str(side / ".git")], check=True)
    change = diff(base, head)
    rules = "\n\n".join((base / f).read_text() for f in ("AGENTS.md", "CONTRIBUTING.md"))
    if len(change) > DIFF_LIMIT:
        result, why = None, f"the change is {len(change)} characters; split it (limit {DIFF_LIMIT})"
    elif not change:
        result, why = None, "the pull request changes nothing"
    else:
        result, why = review(base / "scripts" / "review" / "prompt.md", rules, change)
    approved = (result is not None and result["verdict"] == "approve"
                and len(result["criteria"]) >= CRITERIA and all(c["holds"] for c in result["criteria"]))
    lines = [result["summary"]] if result else [why]
    if result:
        lines += [f"{'holds' if c['holds'] else 'FAILS'}: {c['criterion']} -- {c['evidence']}"
                  for c in result["criteria"]]
    title = "APPROVED" if approved else "REJECTED"
    body = "\n".join([f"### Independent review: {title}", ""] + [f"- {l}" for l in lines])
    (a.out / "comment.md").write_text(body + "\n")
    print(body)
    return 0 if approved else 1


if __name__ == "__main__":
    sys.exit(main())
