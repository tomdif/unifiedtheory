#!/usr/bin/env python3
"""Independently verify the actual evolution out of the restricted neutral closure."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalClockFloorTransitionDerivative': 5, 'KFCausalChargedPairTransitionInitial': 6, 'KFCausalChargedPairEvolutionEscape': 7}
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    logs = args.overlay.resolve() / "quantum-charged-pair-evolution-audit"
    report = json.loads((root / "data/quantum_charged_pair_evolution_audit.json").read_text())
    assert report["previous_report"] == dict(path="data/quantum_charged_pair_hamiltonian_audit.json",
        sha256="3fbdabc6b69340ebe6b3a0668e4ca82647d65240bb125a04d3f05277c1479490")
    parent_path = root / report["previous_report"]["path"]
    assert digest(parent_path) == report["previous_report"]["sha256"]
    parent = json.loads(parent_path.read_text())
    assert len(parent["source_sha256"]) == 2196
    assert len(report["source_sha256"]) == 2201
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
    assert source.endswith(suffix) and len(source.splitlines()) == 8019
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
          + " new theorem audits, 2201 source hashes preserving all 2196, exact three-import root append,"
          + " inherited numerical evidence and Hermite research checkpoint unchanged, no new .lake artifacts.")


if __name__ == "__main__":
    main()

