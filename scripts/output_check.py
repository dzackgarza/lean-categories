#!/usr/bin/env python3
"""How much of the recent history realized definitions, and whether it touched the scheduler.

A commit counts as a realization when it adds `[realized]` to a mapping row that did not carry
it before, or when it rewrites a `[realized]` row together with Lean source (a false realization
rebuilt as an actual construction). Everything else — selector refreshes, records, acceptance
passes, reclassification, row edits without Lean — is not.
Run before choosing the next unit (AGENTS.md, "Definitions are constructed, not deferred").
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys

UNIT = re.compile(r"^[+-]\|\s*`([A-Z0-9]+-[A-Z0-9-]+)`")
SCHEDULER = (
    "scripts/foundational_frontier.py",
    "scripts/foundational_definition_index.py",
    "tests/test_foundational_frontier.py",
)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout


def realized_rows(commit: str) -> tuple[set[str], set[str]]:
    """Rows newly marked `[realized]`, and `[realized]` rows rewritten in place."""
    before: set[str] = set()
    after: set[str] = set()
    for line in git("show", "--format=", "--unified=0", commit, "--", "corpus").splitlines():
        match = UNIT.match(line)
        if not match or "[realized]" not in line:
            continue
        (after if line.startswith("+") else before).add(match.group(1))
    return after - before, after & before


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-n", type=int, default=20, help="how many recent commits to read")
    args = parser.parse_args()

    # Judge only work done under the current rules: a window reaching back past the last change
    # to the governing section would tell a freshly corrected worker to stop and re-diagnose
    # history that has already been diagnosed.
    baseline = git(
        "log", "-1", "--format=%H", "-S", "## Definitions are constructed, not deferred", "--", "AGENTS.md"
    ).strip()
    span = [f"{baseline}..HEAD"] if baseline else []
    commits = git("log", f"-{args.n}", "--format=%h%x09%s", *span).splitlines()
    if len(commits) < 5:
        print(f"{len(commits)} commits since the governing rules last changed; too few to judge. Carry on.")
        return 0
    realizing = 0
    for entry in commits:
        commit, subject = entry.split("\t", 1)
        new, rewritten = realized_rows(commit)
        touched = git("show", "--format=", "--name-only", commit).splitlines()
        scheduler = [path for path in touched if path in SCHEDULER]
        rebuilt = rewritten if any(path.endswith(".lean") for path in touched) else set()
        if new or rebuilt:
            realizing += 1
            mark = f"realized {len(new)}" if new else f"rebuilt {len(rebuilt)}"
        else:
            mark = "no realization"
        flag = f"  SCHEDULER CHANGED: {', '.join(scheduler)}" if scheduler else ""
        print(f"{commit}  {mark:<16} {subject[:70]}{flag}")

    share = realizing / len(commits) if commits else 0.0
    print(f"\n{realizing} of {len(commits)} recent commits realized a definition ({share:.0%}).")
    if share < 0.5:
        print(
            "Below half: stop selecting units. Read these commits, name the rule or constraint being "
            "cycled on, and fix that governing text (or file it for the owner) before more repairs."
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
