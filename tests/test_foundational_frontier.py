import re
import sys
import unittest
from dataclasses import replace
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import foundational_frontier as frontier


class DefinitionReadinessTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        corpus = REPO_ROOT / "corpus"
        cls.units = frontier.parse_catalogue(
            corpus / "foundational-corpus-units-fc05-weibel.md"
        )
        cls.mappings = frontier.parse_mappings(corpus)
        for unit_id in (
            "FC05-C09-U124",
            "FC05-C10-U081",
            "FC05-C10-U083",
            "FC05-C10-U085",
        ):
            mapping = cls.mappings[unit_id]
            cls.mappings[unit_id] = replace(
                mapping,
                verdict=re.sub(r"\s*\[realized\]", "", mapping.verdict, flags=re.I),
                row=re.sub(r"\s*\[realized\]", "", mapping.row, flags=re.I),
            )
            if cls.mappings[unit_id].delivered:
                raise AssertionError(
                    f"{unit_id}: regression fixture requires its real route in an "
                    "unrealized state"
                )
        cls.catalogue = {unit.unit_id: unit for unit in cls.units}

    def blockers(self, unit_id: str) -> tuple[str, ...]:
        return frontier.unit_blockers(
            "Definitions",
            self.catalogue[unit_id],
            self.mappings,
            self.catalogue,
        )

    def test_mapping_prerequisite_survives_theorem_labelled_catalogue_edge(self) -> None:
        self.assertEqual(self.blockers("FC05-C10-U085"), ("FC05-C10-U081",))

    def test_blocked_marker_schedules_representation_repair(self) -> None:
        unit = frontier.Unit(
            "FC99-C01-U001",
            "Definition/result — synthetic representation repair fixture",
            "synthetic mixed source unit",
            (),
        )
        mapping = frontier.Mapping(
            "[definition-only] [sweep-iii-blocked] synthetic representation repair",
            "unmatched",
            "synthetic.md",
            "[definition-only] [sweep-iii-blocked] [residue-search-audited]",
        )
        mappings = {unit.unit_id: mapping}
        catalogue = {unit.unit_id: unit}
        self.assertTrue(mapping.sweep_iii_blocked)
        self.assertEqual(
            frontier.unit_blockers("Definitions", unit, mappings, catalogue),
            (),
        )
        self.assertTrue(frontier.is_theorem(unit, mapping))

    def test_effective_prerequisites_explain_the_blocker(self) -> None:
        unit = self.catalogue["FC05-C10-U085"]
        self.assertEqual(
            frontier.effective_dependencies(
                "Definitions", unit, self.mappings[unit.unit_id]
            ),
            ("FC05-C10-U083", "FC05-C10-U081"),
        )

    def test_explicit_theorem_prerequisite_is_result_layer_blocker(self) -> None:
        unit = self.catalogue["FC05-C10-U085"]
        mappings = dict(self.mappings)
        mappings[unit.unit_id] = replace(
            mappings[unit.unit_id],
            row=mappings[unit.unit_id].row.replace(
                "Construction prerequisites: `FC05-C10-U081`.",
                "Construction prerequisites: `FC05-C10-U083`.",
            ),
        )
        self.assertEqual(
            frontier.unit_blockers("Definitions", unit, mappings, self.catalogue),
            ("Sweep-IV result layer",),
        )

    def test_ordinary_mapping_citation_is_not_a_scheduler_edge(self) -> None:
        unit = self.catalogue["FC05-C10-U030"]
        mapping = self.mappings[unit.unit_id]
        self.assertIn("FC05-C10-U029", mapping.row)
        self.assertEqual(frontier.construction_dependencies(unit, mapping), ())

    def test_malformed_construction_prerequisite_fails_loudly(self) -> None:
        unit = self.catalogue["FC05-C10-U085"]
        mappings = dict(self.mappings)
        mappings[unit.unit_id] = replace(
            self.mappings[unit.unit_id],
            row=self.mappings[unit.unit_id].row.replace(
                "Construction prerequisites: `FC05-C10-U081`.",
                "Construction prerequisites: FC05-C10-U081",
            ),
        )
        with self.assertRaises(ValueError):
            frontier.validate_phase_classification(self.units, mappings)

    def test_duplicate_markers_in_one_cell_fail_loudly(self) -> None:
        unit = self.catalogue["FC05-C10-U085"]
        mappings = dict(self.mappings)
        mappings[unit.unit_id] = replace(
            mappings[unit.unit_id],
            row=mappings[unit.unit_id].row.replace(
                "Construction prerequisites: `FC05-C10-U081`.",
                "Construction prerequisites: `FC05-C10-U083`. "
                "Construction prerequisites: `FC05-C10-U081`.",
            ),
        )
        with self.assertRaises(ValueError):
            frontier.validate_phase_classification(self.units, mappings)

    def test_unknown_explicit_prerequisite_fails_loudly(self) -> None:
        unit = self.catalogue["FC05-C10-U085"]
        mappings = dict(self.mappings)
        mappings[unit.unit_id] = replace(
            mappings[unit.unit_id],
            row=mappings[unit.unit_id].row.replace(
                "FC05-C10-U081`.", "FC05-C10-U999`.",
            ),
        )
        with self.assertRaises(ValueError):
            frontier.validate_phase_classification(self.units, mappings)

    def test_unmatched_local_realization_must_preserve_residue_audit(self) -> None:
        unit = frontier.Unit(
            "FC99-C01-U001",
            "Definition / construction",
            "raw construction",
            (),
        )
        mapping = frontier.Mapping(
            "[definition-only] transcribed locally",
            "unmatched",
            "synthetic.md",
            "FC99-C01-U001 [definition-only] unmatched "
            "local source transcription 2026-09-20",
        )
        with self.assertRaisesRegex(
            ValueError, "erased State-1 residue-search provenance"
        ):
            frontier.validate_phase_classification(
                [unit], {unit.unit_id: mapping}
            )

    def test_unmatched_local_realization_accepts_preserved_residue_audit(self) -> None:
        unit = frontier.Unit(
            "FC99-C01-U001",
            "Definition / construction",
            "raw construction",
            (),
        )
        mapping = frontier.Mapping(
            "[definition-only] transcribed locally [residue-search-audited]",
            "unmatched",
            "synthetic.md",
            "FC99-C01-U001 [definition-only] unmatched [residue-search-audited] "
            "local source transcription 2026-09-20",
        )
        frontier.validate_phase_classification([unit], {unit.unit_id: mapping})

    def test_independent_reference_port_remains_ready(self) -> None:
        self.assertEqual(self.blockers("FC05-C09-U124"), ())

    def test_negative_realized_mention_does_not_deliver_reference_port(self) -> None:
        mapping = frontier.Mapping(
            "[definition-only] [sweep-iii-blocked] pending port",
            "reference-port",
            "synthetic.md",
            "pending port; not marked `[realized]` until theorem-layer input exists",
        )
        self.assertFalse(mapping.realized)
        self.assertFalse(mapping.delivered)

    def test_legacy_realized_by_provenance_remains_supported(self) -> None:
        mapping = frontier.Mapping(
            "exact reference port",
            "reference-port",
            "synthetic.md",
            "exact reference port; [realized] by `Owner.definition`",
        )
        self.assertTrue(mapping.realized)
        self.assertTrue(mapping.delivered)

    def test_ready_selection_keeps_independent_unit_and_excludes_blocked_unit(self) -> None:
        pending = [
            unit
            for unit in frontier.phase_units("Definitions", self.units, self.mappings)
            if not frontier.unit_delivered("Definitions", unit, self.mappings)
        ]
        selected = {
            unit.unit_id
            for unit in frontier.next_open_units(
                "Definitions",
                pending,
                self.mappings,
                self.catalogue,
                limit=len(pending),
            )
        }
        self.assertIn("FC05-C09-U124", selected)
        self.assertNotIn("FC05-C10-U085", selected)

    def test_current_result_units_do_not_become_definition_prerequisites(self) -> None:
        corpus = REPO_ROOT / "corpus"
        cases = (
            ("FC10", "foundational-corpus-units-fc10-serre-local-fields.md", "FC10-C04-U002"),
            ("FC10", "foundational-corpus-units-fc10-serre-local-fields.md", "FC10-C04-U005"),
            ("FC17", "foundational-corpus-units-fc17-kerodon.md", "FC17-KER-U02698"),
        )
        source_indexes = {}
        for source_id, filename, unit_id in cases:
            if source_id not in source_indexes:
                units = frontier.parse_catalogue(corpus / filename)
                source_indexes[source_id] = {unit.unit_id: unit for unit in units}
            catalogue = source_indexes[source_id]
            self.assertEqual(
                frontier.unit_blockers(
                    "Definitions",
                    catalogue[unit_id],
                    self.mappings,
                    catalogue,
                ),
                ("Sweep-IV result layer",),
            )


if __name__ == "__main__":
    unittest.main()
