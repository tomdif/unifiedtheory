#!/usr/bin/env python3
"""Independently verify the common-width neutral response checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalNeutralWidthUniformGrowth': 6, 'KFCausalReciprocalNeutralCommonWidthKernel': 9, 'KFCausalReciprocalNeutralCommonWidthResponse': 4}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    logs = args.overlay.resolve() / "quantum-common-width-neutral-response-audit"
    report = json.loads((root / "data/quantum_common_width_neutral_response_audit.json").read_text())
    assert report["previous_report"] == dict(path="data/quantum_joint_whole_clock_transport_audit.json",
        sha256="66969ec1f3595c57cca7a83ea8381bb100f0995f54798b54391b7aba0f6307f5")
    parent_path = root / report["previous_report"]["path"]
    assert digest(parent_path) == report["previous_report"]["sha256"]
    parent = json.loads(parent_path.read_text())
    assert len(parent["source_sha256"]) == 2517
    assert len(report["source_sha256"]) == 2524
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
    assert source.endswith(suffix) and len(source.splitlines()) == 8272
    assert hashlib.sha256(source[:-len(suffix)].encode()).hexdigest() == parent["root_check"]["source_sha256"]
    assert digest(root / "UnifiedTheory.lean") == report["root_check"]["source_sha256"]
    assert report["root_check"]["appended_imports"] == list(EXPECTED)
    assert report["root_check"]["exit_code"] == 0 and report["root_check"]["empty_log"]
    assert digest(logs / "root-import.log") == report["root_check"]["log_sha256"]
    assert not (logs / "root-import.log").read_text().strip()
    evidence = dict(parent["numerical_evidence"])
    evidence.update({'joint_neutral_hermite_scan': {'path': 'data/joint_neutral_hermite_response_probe.json', 'sha256': '43a1276e2c2041947dbf8adfadf5c0a83a39a48e1037794c0fca8d1c83325b9d'}, 'joint_neutral_hermite_verification': {'path': 'data/joint_neutral_hermite_response_verification.json', 'sha256': 'd9e0ffde47fe633518cd5f68f478aefda0969fac69f6abdba3687504d0ec31bb'}})
    assert report["numerical_evidence"] == evidence
    for item in report["numerical_evidence"].values():
        if isinstance(item, dict) and "path" in item:
            assert digest(root / item["path"]) == item["sha256"]
    numerical = json.loads((root / evidence["joint_neutral_hermite_scan"]["path"]).read_text())
    verified = json.loads((root / evidence["joint_neutral_hermite_verification"]["path"]).read_text())
    assert numerical["parent_report"] == report["previous_report"]
    assert verified["report_sha256"] == evidence["joint_neutral_hermite_scan"]["sha256"]
    assert verified["verifier_sha256"] == digest(root / "scripts/verify_joint_neutral_hermite_response.py")
    assert verified["passed"] and verified["test_count"] == 525 and verified["rejected_cases"] == 0
    assert verified["source_sha256"] == numerical["source_sha256"]
    assert all(digest(root / p) == h for p, h in numerical["source_sha256"].items())
    assert report["lean_toolchain"] == (root / "lean-toolchain").read_text().strip()
    print("Independent verification passed: " + str(count)
          + " new theorem audits, 2524 source hashes preserving all 2517, exact 3-import root append,"
          + " parent evidence preserved and Hermite diagnostics pinned, no new .lake artifacts.")


if __name__ == "__main__":
    main()

