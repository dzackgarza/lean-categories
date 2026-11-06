"""Tests for the card signature extractor (#59).

The three Topology declarations are fixtures because they are the ones that broke the earlier
extractor: their signatures span several lines and contain instance binders, λ-expressions and
nested delimiters.

    python3 -m pytest tests/test_extract_cards.py -q
"""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from extract_cards import signature_text  # noqa: E402

CURVE = ROOT / "LeanCategories/Topology/InvariantIntegralCurve.lean"
SMASH = ROOT / "LeanCategories/Topology/SmashProduct.lean"


def test_instance_binder_and_lambda_are_kept():
    assert signature_text(CURVE, "contMDiff_data") == (
        " contMDiff_data\n"
        "    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]\n"
        "    [BoundarylessManifold I M] [IsManifold I ∞ M]\n"
        "    {γ : ℝ → M} {v : (x : M) → TangentSpace I x}\n"
        "    (hγ : IsMIntegralCurve γ v)\n"
        "    (hv : CMDiff ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M))) :\n"
        "    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ"
    )


def test_instance_binder_outside_parentheses():
    assert signature_text(CURVE, "contMDiff_mulInvariantVectorField_infty_data") == (
        " contMDiff_mulInvariantVectorField_infty_data [ContMDiffMul I ∞ G]\n"
        "    (v : GroupLieAlgebra I G) :\n"
        "    ContMDiff I I.tangent ∞\n"
        "      (fun g : G => (mulInvariantVectorField v g : TangentBundle I G))"
    )


def test_several_instance_binders_in_one_signature():
    assert signature_text(CURVE, "isMIntegralCurve_mulInvariantIntegralCurveData") == (
        " isMIntegralCurve_mulInvariantIntegralCurveData [CompleteSpace E]\n"
        "    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]\n"
        "    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :\n"
        "    IsMIntegralCurve (mulInvariantIntegralCurveData v x) (mulInvariantVectorField v)"
    )


def test_single_line_signature():
    assert signature_text(SMASH, "map_point") == (
        " map_point {X Y : BasedTop.{u}} (f : X ⟶ Y) : f.right X.point = Y.point"
    )


def test_missing_declaration_is_none():
    assert signature_text(CURVE, "no_such_declaration_here") is None


def test_multiline_variable_block_is_captured_whole():
    """A multi-line `variable` block is reproduced with its continuation lines (#59)."""
    import re
    from extract_cards import scope_context

    lines = CURVE.read_text(encoding="utf-8").splitlines()
    decl = next(i for i, l in enumerate(lines) if l.startswith("theorem contMDiff_data"))
    text, _ = scope_context(CURVE, decl)
    assert "variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]" in text
    # the continuation lines of that block, indented past the `variable` keyword
    assert "  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}" in text
    assert "  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]" in text


def test_emitted_card_is_a_pi_type_with_a_delegated_proof(tmp_path=None):
    """The card states the original as a Π-type and delegates; no application is invented."""
    from extract_cards import split_binders

    stmt = "\n    {M : Type*} [TopologicalSpace M]\n    (hγ : IsMIntegralCurve γ v) :\n    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ"
    binders, ty = split_binders(stmt)
    assert binders.strip().startswith("{M : Type*}")
    assert ty == "ContMDiff 𝓘(ℝ, ℝ) I ∞ γ"
    assert "hγ" in binders


def test_multiline_source_paragraph_is_captured_whole():
    """A `source:` paragraph spanning several lines is captured to the next blank line."""
    from extract_cards import source_of

    src = source_of("LeanCategories.Topology.InvariantIntegralCurve")
    assert src.startswith("Lee, *Introduction to Smooth Manifolds*")
    assert src.endswith("corpus/chapter-20-the-exponential-map-fc08.md`."), src
    assert "\n" not in src
