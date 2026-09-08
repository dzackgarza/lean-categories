# Mathematical issues and papercuts

Capture issues as they arise under [LC-05](CONTRIBUTING.md#lc-05--record-mathematical-issues-and-papercuts-when-encountered).
Use this file for unresolved observations; [TODO.md](TODO.md) and its linked
sweep records own execution dependencies and completion. Entries are not a
certificate that other mathematics has been reviewed.

## Recording an issue

Add a descriptive heading under the appropriate section below. Include:

- **Need:** the intended mathematical objects, maps, hypotheses and laws, or
  the user action and expected workflow behavior.
- **Evidence:** the source-unit ID and source passage, declaration/path, or
  exact observed action and result. Distinguish inspected source from execution.
- **Gap and impact:** what fails or remains uncertain, existing partial
  capability, the earliest affected mathematical owner, and its consumers.
- **Coverage:** what was inspected, confidence, and what remains uninspected.
  For absence claims give Searched, Found, Conclusion, Confidence and Gaps.
- **Repair link:** the existing source-unit work, TODO node or upstream issue;
  state the outcome that would resolve this complaint.

Record a source ambiguity as a question, not a proven error. For example,
an endpoint/interior collision omitted from a simple-loop predicate is a
defining-condition issue; its entry needs the source condition and an actual
separating example, not merely a missing method name.

Search existing entries before adding one. Preserve concurrent entries. On
resolution, verify the full unmet requirement, preserve any unfinished part,
and put resolution evidence in the fixing commit. Logging is not repair and
does not justify weakening a dependent theorem or starting unrelated work.

## Mathematical issues

## Workflow papercuts
