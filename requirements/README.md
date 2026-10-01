# Requirements

Every pull request that adds or changes mathematics here includes the requirement it answers, as a
file in this directory (CONTRIBUTING LC-17; checked by the independent review,
`scripts/review/prompt.md`, criterion 3).

A requirement states mathematics and its sources only: the objects, maps and properties wanted, and
where they are defined (a textbook, a paper, Mathlib). It never carries anything from downstream:
a goal or term as a kernel, language or test forms it, a failing statement or suite output, how
something must be stated or registered for a consumer to accept it, or a choice of definitions
motivated by what a consumer can read or compute.

The formalization author's prompt is the requirement file, verbatim. A request that arrives with
downstream content is answered by rewriting it as mathematics before any work starts, or refused.
