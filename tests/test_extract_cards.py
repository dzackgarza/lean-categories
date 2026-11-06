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
