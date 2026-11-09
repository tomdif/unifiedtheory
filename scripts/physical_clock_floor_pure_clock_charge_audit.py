#!/usr/bin/env python3
"""Audit exact pure-clock momentum charge symmetry, Born laws and orbit graphs.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_pure_clock_charge_audit.py --overlay PATH

Sequential direct Lean checks rebuild seven new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorPureClockPairedCoordinates', 9), ('KFCausalClockFloorPureClockPartialFourier', 2), ('KFCausalClockFloorPureClockChargeCoordinates', 6), ('KFCausalClockFloorPureClockCharge', 7), ('KFCausalClockFloorPureClockChargeGraph', 5), ('KFCausalClockFloorPureClockProbability', 13), ('KFCausalClockFloorPureClockChargeControl', 4)]


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
    logs = overlay/'physical-clock-floor-pure-clock-charge-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_pure_clock_momentum_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_pure_clock_charge_audit.py']
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
        scope='For the existing clock-floor model with epsilon>0 and nonzero hbar, this audit proves exact charge symmetry of the previously constructed selfadjoint pure-clock momentum B, without a small-hbar restriction. The model and Hamiltonian are unchanged. The pure-clock coordinate unitary U0 is identified in actual paired position coordinates as a weighted chart change only in the spectator clock coordinate; the antisymmetric block remains fixed. A clock-only spectator homeomorphism supplies compact support for dense factor tests. Actual L2 product identities and density prove that the partial Fourier transform commutes with U0 in these paired coordinates. Its whole-L2 representative is then proved in the actual mixed charge coordinates. The actual frequency-normalized charge rotation fixes the clock and commutes with that chart and weight, establishing U0 charge commutation, inverse-coordinate charge commutation and pure-clock transport charge commutation on every physical L2 state. Differentiation of this actual group identity proves charge invariance of the full maximal B graph and domain, including equality of output norms. This requires no compact-state core, assumed group commutation, charge-zero state or Hamiltonian-domain invariance. The actual finite B Born measure is constructed from the canonical Fourier momentum law through U0 inverse, with total mass norm(f)^2 and probability normalization for unit vectors. Its characteristic equals inner(f,W(hbar*v)f) for the actual pure-clock transport W. The entire measure and both spectral tails are exactly charge invariant and unchanged by normalized charge averaging, on arbitrary L2 states without momentum-domain premises. Actual B graph outputs give R^2*tail<=norm(Bf)^2 and the corresponding outside-interval measure bound. Square-integrable charge-orbit graph outputs are equivalent to B-domain membership; extraction yields an actual Bf with squared norm exactly the charge-orbit output squared L2 norm. The same norm bounds both tails. Families with actual B outputs uniformly bounded in squared norm have tight Born laws, including varying positive floors and nonzero hbar. These last bounds are implications from explicit graph-output bounds; no such bound is assumed or established along the Hamiltonian evolution. This closes the pure-clock observable charge-symmetry gap. It does not prove its commutator with the ordered vacuum factor, the kinetic and matter momentum responses, a charge-averaged Hamiltonian force bound, a momentum Ehrenfest law with cutoff removal, or quantum clock escape. Coupled longitudinal momentum L remains distinct and non-charge-invariant; its positive vacuum response cannot be transferred to B by dropping the transverse shear term. Compact states have not yet been shown to be a B graph core, and maximal-domain equality with the unclosed RPR composition is not asserted. Evolved canonical momentum control, closed joint phase-space dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. All 1267 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_pure_clock_charge_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
