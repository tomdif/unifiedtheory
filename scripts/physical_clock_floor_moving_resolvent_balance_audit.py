#!/usr/bin/env python3
"""Audit the current-time resolvent commutator balance and its vanishing correction.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_moving_resolvent_balance_audit.py --overlay PATH

Sequential direct Lean checks rebuild nine new modules, audit their axioms,
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


MODULES = [('KFCausalMovingObservableDerivative', 2), ('KFCausalFormResolventEnergyBounds', 4), ('KFCausalMovingSandwichCalculus', 6), ('KFCausalClockFloorResolventEnergyControl', 9), ('KFCausalClockFloorMovingResolvent', 12), ('KFCausalFormResolventCommutator', 1), ('KFCausalClockFloorMovingResolventEhrenfest', 8), ('KFCausalClockFloorMovingResolventWindow', 10), ('KFCausalClockFloorCanonicalMovingBalance', 8)]


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
    logs = overlay/'physical-clock-floor-moving-resolvent-balance-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_resolvent_balance_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_moving_resolvent_balance_audit.py']
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
        scope='For the actual averaged Hamiltonian at the current time t, the scaled resolvent R_Lambda(t)=Lambda*(Lambda+H_t)^-1 has an operator-norm time derivative S_Lambda(t). Its operator norm is at most 1/2. On every completed form state x, norm(S_Lambda(t) Jx)^2 is at most E_t(x)/Lambda. These follow from a constructed growing-output Gram factorization, resolvent energy smoothing and energy contraction, without a Hamiltonian operator-domain assumption on x. A general moving-observable chain rule requires only continuity of the physical state and the already-derived frozen-observable derivative. It gives the exact derivative of the actual expectation of R_Lambda(t) D R_Lambda(t) for every bounded physical D: the leading rate is (i*Lambda/hbar)*inner(psi,(D R_Lambda(t)-R_Lambda(t) D)psi), plus the explicit time correction inner(psi,(S_Lambda D R_Lambda+R_Lambda D S_Lambda)psi). The leading rate is a bounded physical resolvent commutator pairing at every positive Lambda and nonzero hbar; no uniform bound in the joint parameter limit is asserted. The correction has norm at most 2*norm(D)*norm(psi)*sqrt(E_t/Lambda). Both rates are continuous and the exact derivative integrates between arbitrary endpoints. For the actual normalized canonically boosted states with positive fixed floor and width, nonnegative mass-squared, quartic and vacuum coefficients, and an admissible nonzero hbar sequence tending to zero, one eventual index threshold works for all positive Lambda, all bounded contraction tests and all times/endpoints in each finite symmetric window. Set B=exp(2*T)*initialBudget. The correction is at most 2*sqrt(B/Lambda). The difference between the integral of the leading bounded commutator rate and the ORIGINAL observable increment is at most 4*sqrt(B/(4*Lambda))+4*abs(T)*sqrt(B/Lambda). Both errors vanish along every positive Lambda sequence tending to infinity, simultaneously with hbar tending to zero, with no assumed relation between the scales, arbitrary moving contraction tests and bounded moving endpoints. The complete canonical Weyl family is explicitly included, with a physical rate formula and exact identification of original evolved characteristics; canonical frequencies may move arbitrarily. The earlier frozen-time form-rate balance remains intact. The new leading rate is expressed entirely using bounded physical resolvents and canonical tests, and the moving-time correction is proved negligible. A classical Poisson-bracket or transport limit of the normalized resolvent commutator is not derived. Bare phase-test form invariance, uniform normalized commutator control, neutral-position and negative-clock-momentum control, full twelve-dimensional tightness and probability evolution, subsequence independence, late-time zero clock defect, fixed-hbar recovery, floor removal, physical GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed, and no necessity of changing the model is established. All 923 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_moving_resolvent_balance_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
