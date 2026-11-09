#!/usr/bin/env python3
"""Audit full shear/vacuum graph symmetry, composition commutation and a joint core.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_shear_vacuum_audit.py --overlay PATH

Sequential direct Lean checks rebuild eight new modules, audit their axioms,
check the root import, and preserve the preceding source hash chain.
This does not invoke lake build and is not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalFourierLinearChange', 6), ('KFCausalL2FourierLinearChange', 4), ('KFCausalTransverseShearEuclidean', 6), ('KFCausalTransverseShearFourier', 2), ('KFCausalClockFloorShearExponential', 8), ('KFCausalClosedOperatorUnitaryCommutation', 9), ('KFCausalClockFloorShearVacuumGraph', 8), ('KFCausalClockFloorJointMomentumCore', 5)]


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    assert 'LEAN_PATH' in os.environ, 'Run with lake env python3.'
    assert overlay.is_dir(), 'Use the verified dependency overlay.'
    env = os.environ.copy()
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    logs = overlay/'physical-clock-floor-shear-vacuum-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_transverse_shear_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_shear_vacuum_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    appended_imports = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name, _ in MODULES)
    assert root_text.endswith(appended_imports), 'Expected only the new appended root imports.'
    assert hashlib.sha256(root_text[:-len(appended_imports)].encode()).hexdigest() == previous['root_check']['source_sha256']
    for name, _ in MODULES:
        assert 'import UnifiedTheory.Audit.'+name in root_text

    checks = []
    for name, count in MODULES:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (root/source).read_text()), source
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0, f'{name}: exit {result.returncode}; see {log}'
        assert not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        assert len(audits) == count, (name, len(audits), count)
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected, (name, expected)
        declarations = {}
        for declaration, axioms in audits:
            used = {s.strip() for s in axioms.split(',') if s.strip()}
            assert used <= STANDARD_AXIOMS, (declaration, used)
            declarations[declaration] = sorted(used)
        checks.append(dict(source=source, command=command, exit_code=result.returncode,
                           log_sha256=sha256(log), audited_declarations=declarations))
        print(name, ': compiled;', count, 'standard-axiom audits', flush=True)

    result = subprocess.run(['lean', '-j1', 'UnifiedTheory.lean'], cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert root_hash == sha256(root/'UnifiedTheory.lean'), 'Root changed during verification.'
    assert previous_hash == sha256(previous_path), 'Previous report changed during verification.'
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='For the existing clock-floor model, this audit proves full maximal-graph invariance of the unbounded longitudinal exponential E_a=exp(aL) and ordered vacuum factor T=exp(L/2)R under the actual transverse shear S(t). A determinant-weighted Fourier change-of-variables formula is derived for any invertible finite-dimensional real linear map, then extended to all L2 states for the actual weighted unitary by Schwartz density and null-set preservation. The physical shear is identified as an actual Euclidean linear map; its inverse-adjoint dual fixes clock frequency exactly. The all-L2 Fourier formulas hold in canonical and coupled coordinates with the actual determinant coefficient. No isometry of the transverse coordinate map or spectral commutation premise is assumed. These formulas prove graph and domain invariance in both directions and preservation of graph-output norms for E_a and T. A general closed-operator theorem integrates the orbit inside the closed graph, constructs primitive and average graph pairs, and differentiates graph difference quotients. It proves that for Tf=g and Jf=j, Tj=k iff Jg=k, including equivalence of both composition-domain conditions on Dom(T) intersect Dom(J). Orbit averages construct a dense T graph core with input and output in Dom(J). The generic graph-invariance hypothesis is discharged for the actual E_a and T. The new shear/vacuum results require epsilon>0; momentum interchange requires hbar!=0, without a small-hbar restriction. A further dense T graph core is constructed with input and output in both Dom(L) and Dom(J), by averaging the previously proved L-regular graph core under S and proving that L regularity is preserved. On this common core both JT and TJ exist and agree, while the previously proved LT-TL correction is retained. This joint core and its L composition formula inherit the condition abs(hbar)<=2*pi*epsilon/3 and hbar!=0. All graph-core statements concern graph(T) closure; no density in a stronger joint graph norm is claimed. The identity B=L-C^(-1)J is still proved only on C1 compact physical states by the predecessor, and is not extended to the new vacuum core. No generic compact-state vacuum domain, compact-state momentum graph core, maximal sum-domain identity, B/T commutator, charge-averaged shear force control, or Hamiltonian-evolved J/B output bound is proved. The new shear symmetry is not Hamiltonian evolution or physical charge invariance. Quantum clock escape, evolved momentum tightness, full Hamiltonian response with cutoff removal, closed joint dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. The model and Hamiltonian are unchanged; no necessity or impossibility of a model change is established. All 1284 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_shear_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
