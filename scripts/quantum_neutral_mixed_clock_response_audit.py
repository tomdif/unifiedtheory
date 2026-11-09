#!/usr/bin/env python3
"""Audit the actual neutral potential-response bound with mixed clock profiles."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralMixedClockCrossPairing', 'KFCausalNeutralMixedClockState', 'KFCausalNeutralMixedClockPairing', 'KFCausalNeutralMixedClockPotential', 'KFCausalNeutralMixedClockBound', 'KFCausalNeutralMixedClockCharge']
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    assert overlay.is_dir() and "LEAN_PATH" in os.environ
    env = os.environ.copy()
    env["LEAN_PATH"] = str(overlay) + os.pathsep + env["LEAN_PATH"]
    logs = overlay / "quantum-neutral-mixed-clock-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_superposition_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "99c87259e8e75f9c938501f7b41a7acabd35d3a59cb9248190d16509d4c790de"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_mixed_clock_response_audit.py",
        "scripts/verify_quantum_neutral_mixed_clock_response.py",
    ]
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    for item in evidence.values():
        if isinstance(item, dict) and "path" in item:
            assert sha(root / item["path"]) == item["sha256"]
    root_text = (root / "UnifiedTheory.lean").read_text()
    suffix = "".join("import UnifiedTheory.Audit." + n + "\n" for n in MODULES)
    assert root_text.endswith(suffix)
    assert hashlib.sha256(root_text[:-len(suffix)].encode()).hexdigest() == previous["root_check"]["source_sha256"]
    root_hash = sha(root / "UnifiedTheory.lean")
    checks = []
    for name in MODULES:
        source = "UnifiedTheory/Audit/" + name + ".lean"
        text = (root / source).read_text()
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", text)
        command = ["lean", "-j1", "-o", str(overlay / "UnifiedTheory/Audit" / (name + ".olean")), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / (name + ".log")
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r": error|: warning|sorryAx", result.stdout), str(log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        audits = {n: sorted(s.strip() for s in xs.split(",") if s.strip()) for n, xs in parsed}
        expected = {"UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^#print axioms (\S+)", text, re.M)}
        declared = {"UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^theorem (\S+)", text, re.M)}
        assert len(parsed) == len(audits) and set(audits) == expected == declared
        assert all(set(xs) <= ALLOWED for xs in audits.values())
        checks.append(dict(source=source, command=command, exit_code=0,
                           log_sha256=sha(log), audited_declarations=audits))
        print(name + ": clean; " + str(len(audits)) + " theorem dependency lists", flush=True)
    result = subprocess.run(["lean", "-j1", "UnifiedTheory.lean"], cwd=root, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs / "root-import.log"
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert sha(root / "UnifiedTheory.lean") == root_hash and sha(previous_path) == previous_hash
    assert all(sha(root / p) == h for p, h in hashes.items())
    for item in evidence.values():
        if isinstance(item, dict) and "path" in item:
            assert sha(root / item["path"]) == item["sha256"]
    for name in MODULES:
        assert not (root / ".lake/build/lib/lean/UnifiedTheory/Audit" / (name + ".olean")).exists()
    report = dict(
        new_lean_theorem_count=sum(len(c["audited_declarations"]) for c in checks),
        modules=checks, source_sha256=hashes, numerical_evidence=evidence,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        root_check=dict(command=["lean", "-j1", "UnifiedTheory.lean"], exit_code=0,
                        empty_log=True, source_sha256=root_hash, log_sha256=sha(log),
                        appended_imports=MODULES),
        lean_toolchain=(root / "lean-toolchain").read_text().strip(),
        scope='The actual signed ordered-potential response now has a relative lower bound on every finite neutral exponential-polynomial Hilbert state with independent positive clock widths a_i and arbitrary real clock frequencies p_i. For fixed nonzero h there exists M>=0 depending only on groundWidth(h), such that for every epsilon>0 with |h|<=2*pi*epsilon/3, every N, all widths a_i>0, all real p_i, all complex sources b_i and amplitudes C_i and all finite polynomials P_i, R>=-((M+2)/epsilon)*E. The state is the sum of actual PolynomialGaussianDomain.input packets with those parameters, neutralSource(b_i), and polynomial coordinate4. Its actual pure-clock momentum is constructed. Both state and momentum lie in all eight natural energy-factor domains and the physical zero-charge sector; projection fixes the state and its standing charge is zero. E and R use the actual vacuum, field and field-square outputs with unit couplings, weights1,1/2,1/4. Independent-width/frequency cross pairings are identified using the already proved whole-clock integration by parts. All cross densities and reduced response kernels are absolutely integrable. At each clock coordinate, the shifted clock amplitude of each packet is absorbed into its own complex coefficient. The reduced energy and response become exactly the previous neutral finite kernels with those coefficients held fixed. No derivative of the absorbed clock coefficients is discarded: clock slopes have already canceled in the exact integrated response identity. The previous uniform local bound can therefore be applied separately at every clock position, then integrated to the actual signed response. The same constant is independent of all widths and frequencies and all source counts, coefficients and polynomial degrees. This removes the common-clock restriction from the previous result. It does not prove density in the full required energy/response graph domain, preservation of this neutral family under full physical evolution, a bound for charged excitations, full Hamiltonian response control, negative-tail tightness, unconditional clock recovery, regulator or physical limits, Standard Model or general-relativity identification, octonion necessity or a physical TOE. No necessary model revision is shown. Thirty-nine public theorem checks in six modules use only standard axioms. All 2140 predecessor source hashes and inherited numerical evidence are preserved in 2148 entries. Exactly six root imports are appended and no new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_mixed_clock_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

