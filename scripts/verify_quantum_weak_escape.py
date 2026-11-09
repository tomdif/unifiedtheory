#!/usr/bin/env python3
"""Independently verify actual quantum weak escape and preserved provenance."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalWeightedGraphWeakDecay': 1, 'KFCausalClockFloorDriftDetection': 6, 'KFCausalClockFloorVacuumObservation': 6, 'KFCausalClockFloorQuantumWeakEscape': 5}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    logs = args.overlay.resolve() / "quantum-weak-escape-audit"
    report = json.loads((root / "data/quantum_weak_escape_audit.json").read_text())
    assert report["previous_report"] == dict(path="data/quantum_defect_coercivity_audit.json",
        sha256="41a7e9c484b56c8868f1baa69767873d11d7d9109855d9e713d02bd52d15ede9")
    parent_path = root / report["previous_report"]["path"]
    assert digest(parent_path) == report["previous_report"]["sha256"]
    parent = json.loads(parent_path.read_text())
    assert len(parent["source_sha256"]) == 1774
    assert len(report["source_sha256"]) == 1780
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
    assert source.endswith(suffix) and len(source.splitlines()) == 7712
    assert hashlib.sha256(source[:-len(suffix)].encode()).hexdigest() == parent["root_check"]["source_sha256"]
    assert digest(root / "UnifiedTheory.lean") == report["root_check"]["source_sha256"]
    assert report["root_check"]["appended_imports"] == list(EXPECTED)
    assert report["root_check"]["exit_code"] == 0 and report["root_check"]["empty_log"]
    assert digest(logs / "root-import.log") == report["root_check"]["log_sha256"]
    assert not (logs / "root-import.log").read_text().strip()
    assert report["numerical_evidence"] == parent["numerical_evidence"]
    for item in report["numerical_evidence"].values():
        if isinstance(item, dict) and "path" in item:
            assert digest(root / item["path"]) == item["sha256"]
    assert report["lean_toolchain"] == (root / "lean-toolchain").read_text().strip()
    print("Independent verification passed: " + str(count)
          + " new theorem audits, 1780 source hashes preserving all 1774, exact 4-import root append,"
          + " inherited numerical evidence unchanged, no new .lake artifacts.")


if __name__ == "__main__":
    main()
