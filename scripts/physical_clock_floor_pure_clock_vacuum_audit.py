#!/usr/bin/env python3
"""Audit the extended pure-clock graph identity and actual vacuum commutator.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_pure_clock_vacuum_audit.py --overlay PATH

Sequential direct Lean checks rebuild six new modules, audit their axioms,
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


MODULES = [('KFCausalUnitaryInvariantCore', 8), ('KFCausalClockFloorPureClockTestCore', 9), ('KFCausalSelfAdjointCoreWeakGraph', 3), ('KFCausalClockFloorPureClockJointDomain', 6), ('KFCausalClockFloorPureClockVacuumCommutator', 6), ('KFCausalClockFloorPureClockVacuumResponse', 8)]


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
    logs = overlay/'physical-clock-floor-pure-clock-vacuum-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_shear_vacuum_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_pure_clock_vacuum_audit.py']
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
        scope='For the existing clock-floor model, this audit proves that every state in Dom(L) intersect Dom(J) belongs to the actual selfadjoint pure-clock momentum domain, with Bf=Lf-C^(-1)Jf. The extension is derived rather than assumed. A general invariant-set theorem proves that any dense invariant subset of the actual strong-unitary momentum domain is a graph core, using complete closed-submodule orbit integration, bounded averaging, density and convergence in momentum graph norm. Smooth compact physical states are proved L2 dense, C1 compact states are proved invariant under the actual pure-clock half-density transport, and their actual B-domain membership is already established. Consequently their graph span is a core for the full maximal B graph. A general selfadjoint weak-core theorem and the previously proved compact four-momentum identity then derive the full Dom(L) intersect Dom(J) inclusion and output formula. Bounded C^(-1) is symmetric and preserves the full J graph with commuting outputs. The output bound norm(Bf)<=norm(Lf)+norm(Jf)/epsilon holds on this common domain. These results require epsilon>0 and hbar!=0 without a small-hbar restriction. On the previously constructed dense T=exp(L/2)C^(-1/2) graph core with L and J on input and output, B exists on both input and output, and both BT and TB compositions are constructed. The exact commutator is [B,T]f=[L,T]f-(1/epsilon)(D-Z)J(Tf), where D=epsilon/C and Z is the existing shifted defect. Its norm is bounded by abs(hbar)/(4*epsilon)*norm(Tf)+(2*abs(hbar)/epsilon^2)*norm(D^2 J(Tf)). The actual weak vacuum response (-2/hbar) Im inner(Tf,T(Bf)) is derived on that core, and its difference from the earlier positive longitudinal response is bounded by (4/epsilon^2)*norm(Tf)*norm(D^2 J(Tf)). Lower and upper response bounds retaining this shear error are proved; no positivity of the total pure-clock response is asserted. The vacuum/core results inherit abs(hbar)<=2*pi*epsilon/3. Their density is in graph(T), not a stronger joint momentum graph norm, and no unrestricted BT/TB composition-domain equality is claimed. No reverse maximal sum-domain identity, charge invariance of J or L, charge-averaged shear-force bound, evolved weighted-shear bound, full Hamiltonian B momentum response with cutoff removal, or quantum clock escape is proved. The response is the unscaled ordered-vacuum-factor contribution, not a full Hamiltonian evolution law. Evolved momentum tightness, closed joint dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. The model and Hamiltonian are unchanged; no necessity or impossibility of a model change is established. All 1293 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_pure_clock_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
