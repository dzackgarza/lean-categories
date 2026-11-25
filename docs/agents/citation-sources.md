## Sourcing a citation — the source gate

The reuse gate above governs *formalizations*; this one governs *mathematical sources*. Much of this programme's content is transcribed from the literature — Nikulin's genus theorems, O'Meara's modularity, Conway–Sloane, Kac. **A citation entering a plan, issue, docstring, or commit message carries an item key from the live library and a statement read on the page.**

Before citing any paper, book, or theorem number, in order:

1. **Load the [[zotero/SKILL|zotero]] skill and read through the live library.** It owns the transport: the running Zotero desktop's local API, `lib/zotero.py` in the `zotero-library` repo, `health()` first. Follow it rather than a remembered command surface. The library is what supplies the item key that makes a citation resolvable by a later agent.

2. **Use [[zotero-metadata-proof/SKILL|zotero-metadata-proof]] and [[zotero-pdf-extraction-attachments/SKILL|zotero-pdf-extraction-attachments]]** when the question is whether an item's metadata is right, or whether the text in hand is the item's current extraction child. `get_children` paginates, so confirm the full child list before concluding what attachments an item has.

3. **Transcribe the numbered result, and label its role.** Quote the statement as the source gives it, and say whether it is a *definition* or a *characterization*. The distinction carries the hypotheses and names the auxiliary invariants the definition depends on — which is how a missing ingredient becomes visible (§3.5: implications are theorems, not definitions).

4. **Report searches in the reuse gate's form** — name the scope searched (§10.7).

### Read the Zotero extraction corpus

Search the local Zotero Markdown extractions before searching the web or relying on memory.
The extraction corpus is live under `~/Zotero/storage`; it is not a repository mirror.

```bash
cd /home/dzack/zotero-library
just search 'period domain' -- -C2
just search 'Nikulin' -- -w
```

`just search` performs a case-insensitive regular-expression search over
`*_extracted.md` files. It prints matching lines, the parent Zotero key, and a
`zotero://select` link. Treat this output as a locator. Read the matching Markdown
attachment itself and record the relevant line numbers or page markers. A search miss
means only that the inspected extraction corpus had no match.

### Use the local PDF when the extraction is unclear

The Markdown child is the searchable transcription. When a formula, symbol, page
layout, or OCR passage is unclear, open the PDF child attached to the same parent and
inspect the cited page locally. Resolve its file path from the attachment record's
`links.enclosure` field. This preserves the source identity already established in
Zotero.

Use the local PDF to confirm notation, page numbers, and theorem statements. If the
local PDF needs a new text extraction, route it through [[reading-pdfs/SKILL|reading-pdfs]]
and the managed Zotero extraction workflow. A publisher or web copy is relevant when
the source identity or edition remains unresolved; it is not a presumed improvement to
the local extraction.

When local inspection confirms material OCR defects, add the `bad-ocr` tag to the parent
bibliographic item with `add_item_tags(parent_key, ["bad-ocr"])`. Tag the parent rather
than its PDF or Markdown child so later triage sees the source item.

Resolve the source identity through live Zotero before citing it. Call `health()` first,
then use `get_data(parent_key)` for the parent and paginated `get_children(parent_key)`
to find the child whose `data.contentType` is `text/markdown` and whose filename ends in
`_extracted.md`. Read that file at
`~/Zotero/storage/<attachment-key>/<filename>`. If the desktop or local addon is down,
report that blocker; do not use the cloud API or a translation-server fallback.

The parent item's `data.citationKey` is the Better BibTeX key. Use that exact key in the
target document's citation syntax: `[@key]` in Pandoc Markdown or `\cite{key}` in
LaTeX. Add a locator when the extraction supplies one, for example `[@key, p. 12]`.
Never invent a key, derive one from the author or year, or cite only the Zotero key.
When reporting a source, include its Zotero key, Better BibTeX key, creator, and title.

What this gate buys: a citation that resolves, a statement checked against the page, and the auxiliary notions the source's own definition requires. The third is the one that pays — a definition transcribed from the page brings its ingredients with it, and those ingredients are how the catalogue learns which invariants it still owes.

---
