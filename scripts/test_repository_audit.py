"""Regression checks for the audit's proof-token and axiom-output parsers."""
import unittest
from audit_repository import lean_code
from check_twisted_axioms import validate_output


class AuditParsers(unittest.TestCase):
    def test_nested_comments_strings_and_line_numbers(self):
        source = '/- outer /- sorry -/ admit -/\n"axiom \\" sorry"\n-- unsafe\ntheorem x : True := by sorry\n'
        code = lean_code(source)
        self.assertEqual(len(source), len(code))
        self.assertEqual(source.count("\n"), code.count("\n"))
        self.assertEqual(code.count("sorry"), 1)
        self.assertIn("by sorry", code)
        self.assertNotIn("admit", code)

    def test_missing_axiom_output_is_rejected(self):
        with self.assertRaises(ValueError):
            validate_output("#print axioms X.a\n#print axioms X.b\n", "'X.a' does not depend on any axioms")

    def test_sorry_and_custom_axioms_are_rejected(self):
        for axiom in ["sorryAx", "External.unproved"]:
            with self.assertRaises(ValueError):
                validate_output("#print axioms X.a\n", f"'X.a' depends on axioms: [{axiom}]")

    def test_standard_and_empty_dependencies(self):
        report = validate_output("#print axioms X.a\n#print axioms X.b\n",
                                 "'X.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                                 "'X.b' does not depend on any axioms\n")
        self.assertEqual(report["checked_declarations"], 2)
        self.assertTrue(report["passed"])

    def test_prime_in_lean_declaration_name(self):
        report = validate_output("#print axioms X.lower'\n",
                                 "'X.lower'' depends on axioms: [propext]\n")
        self.assertEqual(report["declarations"], {"X.lower'": ["propext"]})


if __name__ == "__main__":
    unittest.main()
