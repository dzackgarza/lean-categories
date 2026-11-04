# Registry consumer (#49)

A minimal downstream package that consumes the `lean-categories` semantic registry the way a
language frontend does: through a **pinned revision of the remote repository**, at elaboration
time, resolving rows by stable ID.

## Pin

`lakefile.toml` requires the library by git revision:

```toml
[[require]]
name = "lean_categories"
git = "https://github.com/dzackgarza/lean-categories.git"
rev = "30c4ff73b81d9169df4ac5a726e4e6012d550e3c"
```

The revision is a real commit on the remote, so this file alone reproduces the build. There is
no path into a working tree, no generated Sage correspondence, no Python seed, no hand-authored
DOT file and no research branch artifact anywhere in the resolution.

When the first release is tagged, the pin becomes `tag = "v0.1.0"` with no other change. The
repository has no tags yet, which is why the pin is a revision.

## Reproduce

From this directory, with the toolchain pinned by `lean-toolchain`
(`leanprover/lean4:v4.33.0`) and Mathlib at the revision the library pins:

```console
$ lake update   # resolves the pinned revision; the Mathlib cache is reused
$ lake build
Build completed successfully (3761 jobs).
```

The library is cloned and compiled from the pinned revision; only then does the consumer module
elaborate. `run_meta` at the end of `RegistryConsumer.lean` fails the build if any of the
following does not hold.

## What the consumer establishes

1. **Stable-ID resolution.** `cat.sets`, `fun.sets.list` and `cell.sets.list.unit` resolve
   through `RegistrySnapshot.declarationNames?` to declarations that exist *in the pinned
   library*, and every resolved name is a `CasCatalogue.*` or `LeanCategories.*` declaration —
   the consumer cannot invent one. A category row resolves to both its declaration and its
   realization.
2. **Named layers are populated.** `cat.`, `fun.`, `cell.`, `obj.`, `op.` and `mor.` each hold
   rows in the pinned revision, so a release can name the surface it exposes.
3. **Lookup is a real lookup.** An ID the revision does not carry (`cat.does_not_exist`) is
   absent, so the checks above are not satisfied by a constant-true stub.
4. **Fail-loud folds.** Re-registering a checked stable ID is refused, and a derived row over an
   unregistered category is refused. The consumer may add rows; it may not overwrite checked
   meaning or hang an edge on a row the revision does not carry.

Stages 2 (typed expressions) and 3 (operation/method ownership) of the contract in the top-level
`README.md` remain gated on #31/#54 and #28/#53; this package currently certifies stage 1.
