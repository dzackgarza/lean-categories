import sys
import unittest
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

    def test_independent_reference_port_remains_ready(self) -> None:
        self.assertEqual(self.blockers("FC05-C09-U124"), ())


if __name__ == "__main__":
    unittest.main()
