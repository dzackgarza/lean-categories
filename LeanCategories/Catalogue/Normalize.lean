/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Syntax

@[expose] public section

/-!
# Expression normalization

Exact-host refinements collapse immediately:

\[
\operatorname{refine}(\operatorname{host}(A), A) \rightsquigarrow \operatorname{total}(A).
\]

Alias handling lives with the registry map passed in.
-/

namespace LeanCategories

/-- Classifier host table used by the normalizer (least-host ownership). -/
structure ClassifierHostTable where
  hostOf : ClassifierId → Option CategoryId

/-- Alias table: spelling aliases resolve to a canonical category id. -/
structure AliasTable where
  canonicalOf : CategoryId → Option CategoryId

namespace AliasTable

/-- Resolve aliases to a fixed point (acyclic forest). -/
partial def canonicalize (t : AliasTable) (id : CategoryId) : CategoryId :=
  match t.canonicalOf id with
  | none => id
  | some id' =>
    if id' == id then id else t.canonicalize id'

end AliasTable

/-- Normalize a category expression. -/
partial def normalizeCategory
    (hosts : ClassifierHostTable) (aliases : AliasTable) :
    CategoryExpr → CategoryExpr
  | .atom id => .atom (aliases.canonicalize id)
  | .opaque id => .opaque (aliases.canonicalize id)
  | .reference id => .reference (aliases.canonicalize id)
  | .familyApp f args => .familyApp f args
  | .classifierTotal c => .classifierTotal c
  | .pullback left right over => .pullback left right (normalizeCategory hosts aliases over)
  | .constructor k args =>
      .constructor k (args.map (normalizeCategory hosts aliases))
  | .refine base clf route =>
      let base' := normalizeCategory hosts aliases base
      -- Exact-host: refine(host(A), A) ↦ total(A)
      match base', hosts.hostOf clf with
      | .atom hid, some host =>
          if hid == host then .classifierTotal clf
          else .refine base' clf route
      | .classifierTotal c, some host =>
          -- refining the total of a classifier whose host matches is rare; keep
          if hosts.hostOf c == some host && c == clf then .classifierTotal clf
          else .refine base' clf route
      | .reference hid, some host =>
          if hid == host then .classifierTotal clf
          else .refine base' clf route
      | _, _ => .refine base' clf route

/-- After alias canonicalization, equal source/target is identity (no edge). -/
def isIdentityEdge (src tgt : CategoryId) (aliases : AliasTable) : Bool :=
  aliases.canonicalize src == aliases.canonicalize tgt

end LeanCategories
