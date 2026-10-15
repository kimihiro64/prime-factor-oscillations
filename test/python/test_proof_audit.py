"""Keep the Lean axiom audit strict across both report formats."""

import unittest
from unittest.mock import patch

from scripts import proof_audit


class AxiomReportTests(unittest.TestCase):
    def test_mixed_axiom_reports(self) -> None:
        log = (
            "'Example.pure' does not depend on any axioms\n"
            "Example.proved : True\n"
            "'Example.proved' depends on axioms: [propext,\n Quot.sound, Classical.choice]\n"
        )
        with patch.object(proof_audit, "THEOREMS", ("Example.pure", "Example.proved")):
            self.assertEqual(
                proof_audit.axiom_sets(log),
                {
                    "Example.pure": [],
                    "Example.proved": ["Classical.choice", "Quot.sound", "propext"],
                },
            )

    def test_invalid_axiom_reports_rejected(self) -> None:
        invalid = (
            "'Example.proved' depends on axioms: [propext]\n",
            "'Example.pure' does not depend on any axioms\n"
            "'Example.pure' does not depend on any axioms\n"
            "'Example.proved' depends on axioms: [propext]\n",
            "'Example.other' does not depend on any axioms\n"
            "'Example.proved' depends on axioms: [propext]\n",
            "'Example.pure' does not depend on any axioms\n"
            "'Example.proved' depends on axioms: [sorryAx]\n",
            "'Example.pure' does not depend on any axioms\n"
            "'Example.proved' depends on axioms: [Example.researchTarget]\n",
        )
        with patch.object(proof_audit, "THEOREMS", ("Example.pure", "Example.proved")):
            for log in invalid:
                with self.subTest(log=log), self.assertRaises(ValueError):
                    proof_audit.axiom_sets(log)
