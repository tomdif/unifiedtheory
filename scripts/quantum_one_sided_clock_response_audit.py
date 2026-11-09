#!/usr/bin/env python3
"""Audit the one-sided full-clock response criterion and exact integral identity."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalOneSidedIntegral', 'KFCausalOneSidedKernelClockResponse']
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
    logs = overlay / "quantum-one-sided-clock-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_quartic_triple_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "480b64818db64df320d992917281015c432de5df1160a5bdd4da064ef08ad5bd"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_one_sided_clock_response_audit.py",
        "scripts/verify_quantum_one_sided_clock_response.py",
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
        scope='Lean proves that the full-clock lower response estimate needs only an upper kernel derivative bound, not an absolute derivative bound. For any differentiable nonnegative kernel K, epsilon>0, abs(y)<=pi*epsilon/3, C>=0, actual energy E and weak response W integrable on the whole real clock line, and K-prime<=C*K, the theorem gives integral(W)>=-((C+2)/epsilon)*integral(E). A sharper variant requires only K-prime/(exp(s)+epsilon)<=(C/epsilon)*K and does not require C>=0. The general reduced-lower-bound version also permits any real kappa. No dimension, degree, coefficient compactness, positive lower bound on K, endpoint limits, reduced-response integrability, or absolute derivative domination is assumed. A separate full-line calculus theorem constructs endpoint sequences tending to both infinities with integrable boundary values tending to zero, then uses a finite-interval derivative inequality. When the derivative is continuous, the same upper domination proves its absolute integrability using norm(D)<=2*norm(G)-D and interval exhaustion. Consequently, for C1 K, the clock theorem also derives reduced-response integrability and the exact weak/reduced integral identity under the one-sided hypothesis. All eleven public theorem dependency checks in two modules use only standard axioms. This is a general sufficient criterion, not a proof that the criterion holds uniformly in charged excitation degree or along the physical evolution. No larger actual state class, trajectory momentum regularity, unbounded moving-test identity, negative-tail tightness, unconditional clock recovery, physical/regulator limits, SM/GR identification, octonion necessity or physical TOE is established by this checkpoint. No necessary model revision is established. Exploratory charged Wick calculations remain outside the audit and are not mathematical or physical certificates. The prior actual quartic-span response theorem and all 2270 parent source/script hashes remain intact in 2274 entries. Exactly two imports extend the 8074-line parent root to 8076 lines, inherited numerical evidence is unchanged, and no new .lake artifacts are generated.')
    target = root / "data/quantum_one_sided_clock_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

