#!/usr/bin/env python3
"""Audit the neutral resolvent linear response and its joint-limit balance.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_resolvent_linear_audit.py --overlay PATH

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


MODULES = [('KFCausalFormResolventTestPairing', 1), ('KFCausalNeutralOutputLinearResponse', 14), ('KFCausalNeutralResolventResponse', 8), ('KFCausalNeutralResolventContinuity', 7), ('KFCausalDisplacedNeutralResolventDynamics', 9), ('KFCausalNeutralResolventLinearLimit', 7)]


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
    logs = overlay/'physical-clock-floor-neutral-resolvent-linear-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_moving_resolvent_balance_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_resolvent_linear_audit.py']
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
        scope='For the actual charge-averaged Hamiltonian, a form-preserving physical test has a bounded resolvent commutator equal to the original form commutator at the resolvent-regularized state. Specialization to the actual canonical neutral-momentum test at displacement hbar*v supplies an energy bound for (i*Lambda/hbar)*inner(psi,(D R_Lambda(t)-R_Lambda(t) D)psi), uniform over all positive Lambda and bounded nonzero hbar. Energy contraction is proved for the actual resolvent. The exact output transformation is a quadratic polynomial in displacement. The normalized neutral rate equals an explicit linear response plus an explicit quadratic response. On every actual form state, the linear term is at most 2*abs(v)*norm(weightedLinear(energyWeight(m,g,k,0)))*E_t, and the quadratic term is at most 2*abs(hbar)*abs(v)^2*norm(weightedQuadratic(energyWeight(m,g,k,0)))*E_t, independently of positive Lambda. Time independence of the coefficient maps is derived from the actual matter weights. The physical outputs and both response terms are continuous along the actual evolutions. For canonically boosted normalized states with positive fixed floor and width, strictly positive mass-squared, quartic and vacuum coefficients, and any admissible nonzero hbar sequence tending to zero, set B=exp(2*T)*initialBudget. One eventual index threshold controls all positive resolvent scales, all neutral test frequencies and all times in the symmetric finite window. The quadratic remainder tends to zero for arbitrary positive scale sequences, bounded moving neutral frequencies and moving window times; no scale divergence is required for this pointwise linearization. The integral of the explicit linear response differs from the ORIGINAL neutral canonical characteristic increment by at most 4*sqrt(B/(4*Lambda))+4*abs(T)*sqrt(B/Lambda)+4*abs(T)*abs(hbar)*abs(v)^2*norm(weightedQuadratic(energyWeight(m,g,k,0)))*B. This residual tends to zero for every positive Lambda sequence tending to infinity simultaneously with hbar tending to zero, with no relative scale condition, bounded moving frequencies and moving endpoints in the window. Each frequency is fixed within its time integral. This removes the normalized-resolvent-rate control gap for this one neutral-momentum test direction and derives a concrete linear response with a vanishing explicit remainder. The leading response still contains hbar-dependent quantum energy-output correlations and translations; no classical force, Poisson-bracket, or transport limit of those correlations is proved. Uniform normalized commutator control for all remaining canonical directions, bare phase-test averaged-form invariance, full twelve-dimensional tightness and probability evolution, neutral-position and negative-clock-momentum control, subsequence independence, late-time zero clock defect, fixed-hbar recovery, floor removal, physical GR/QFT/Standard Model identification and empirical validity remain open. The resolvent and polynomial errors are distinct from the clock-floor commutator defect. No model or preceding operator changed, and no necessity of changing the model is established. All 933 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_resolvent_linear_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
