#!/usr/bin/env python3
"""Independently verify the reciprocal Gaussian clock momentum Hamiltonian domain."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalAnalyticClockFamily': 4, 'KFCausalSecondShiftClockBounds': 7, 'KFCausalSecondShiftClockGraphs': 8, 'KFCausalSecondShiftReducedOutput': 1, 'KFCausalGaussianMomentumMatterSquare': 8, 'KFCausalReciprocalGaussianMomentumMatterSquare': 4, 'KFCausalReciprocalGaussianMomentumStrongHamiltonian': 6}
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    logs = args.overlay.resolve() / "quantum-reciprocal-gaussian-momentum-domains-audit"
    report = json.loads((root / "data/quantum_reciprocal_gaussian_momentum_domains_audit.json").read_text())
    assert report["previous_report"] == dict(path="data/quantum_reciprocal_gaussian_matter_domains_audit.json",
        sha256="84364c94815b3acd7178cc65c955c318f76d4a5f1f74ea57828f1ebb976fa2c6")
    parent_path = root / report["previous_report"]["path"]
    assert digest(parent_path) == report["previous_report"]["sha256"]
    parent = json.loads(parent_path.read_text())
    assert len(parent["source_sha256"]) == 2335
    assert len(report["source_sha256"]) == 2344
    assert all(report["source_sha256"][p] == h for p, h in parent["source_sha256"].items())
    assert all(digest(root / p) == h for p, h in report["source_sha256"].items())
    assert report["new_lean_theorem_count"] == sum(EXPECTED.values())
    assert [Path(item["source"]).stem for item in report["modules"]] == list(EXPECTED)
    count = 0
    for item in report["modules"]:
        name = Path(item["source"]).stem
        source = (root / item["source"]).read_text()
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", source)
        log_path = logs / (name + ".log")
        assert digest(log_path) == item["log_sha256"] and item["exit_code"] == 0
        log = log_path.read_text()
        assert not re.search(r": error|: warning|sorryAx", log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        names = ["UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^theorem (\S+)", source, re.M)]
        commands = ["UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^#print axioms (\S+)", source, re.M)]
        assert len(parsed) == len(names) == len(commands) == EXPECTED[name]
        assert {n for n, _ in parsed} == set(names) == set(commands)
        axioms = {n: sorted(s.strip() for s in xs.split(",") if s.strip()) for n, xs in parsed}
        assert axioms == item["audited_declarations"]
        assert all(set(xs) <= {"propext", "Classical.choice", "Quot.sound"} for xs in axioms.values())
        assert not (root / ".lake/build/lib/lean/UnifiedTheory/Audit" / (name + ".olean")).exists()
        count += len(parsed)
    source = (root / "UnifiedTheory.lean").read_text()
    suffix = "".join("import UnifiedTheory.Audit." + n + "\n" for n in EXPECTED)
    assert source.endswith(suffix) and len(source.splitlines()) == 8136
    assert hashlib.sha256(source[:-len(suffix)].encode()).hexdigest() == parent["root_check"]["source_sha256"]
    assert digest(root / "UnifiedTheory.lean") == report["root_check"]["source_sha256"]
    assert report["root_check"]["appended_imports"] == list(EXPECTED)
    assert report["root_check"]["exit_code"] == 0 and report["root_check"]["empty_log"]
    assert digest(logs / "root-import.log") == report["root_check"]["log_sha256"]
    assert not (logs / "root-import.log").read_text().strip()
    evidence = dict(parent["numerical_evidence"])
    assert all(digest(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    assert report["numerical_evidence"] == evidence
    for item in report["numerical_evidence"].values():
        if isinstance(item, dict) and "path" in item:
            assert digest(root / item["path"]) == item["sha256"]
    assert report["lean_toolchain"] == (root / "lean-toolchain").read_text().strip()
    print("Independent verification passed: " + str(count)
          + " new theorem audits, 2344 source hashes preserving all 2335, exact 7-import root append,"
          + " inherited numerical evidence and Hermite research checkpoint unchanged, no new .lake artifacts.")


if __name__ == "__main__":
    main()

