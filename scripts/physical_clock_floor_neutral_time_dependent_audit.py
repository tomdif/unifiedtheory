#!/usr/bin/env python3
"""Audit the neutral time-dependent weak equation for finite tensor tests.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_time_dependent_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
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


MODULES = [('KFCausalSpacetimeTriangularIntegral', 6), ('KFCausalSpacetimeTimeTestBalance', 6), ('KFCausalNeutralTensorTestEquation', 9), ('KFCausalNeutralTimeDependentDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-time-dependent-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_global_spacetime_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_time_dependent_audit.py']
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
        scope='The finite-window spacetime force gives the neutral time-dependent weak equation for finite sums of products of bounded continuously differentiable time functions with bounded continuous derivatives and complex Schwartz momentum functions. A measurable time triangle and finite force mass prove product integrability, weighted cumulative-force integrability and an exact Fubini identity. The fundamental theorem of calculus evaluates the time integral on each triangular section. Its linear form expresses the weighted cumulative force as the endpoint time value times the whole-window force integral minus the force tested against the time weight. The global force window is supported on its time interval, and restricting it to a smaller interval recovers the previously constructed interval force. For any scalar observable obeying that cumulative interval balance, weighted time integrability is DERIVED from finite force mass. No time derivative, absolute continuity or extra regularity of the observable is assumed. The generic time integration-by-parts theorem retains both boundary terms and gives a zero right side when both time-test endpoint values vanish. Finite sums of separated time and Schwartz momentum functions define bounded continuous spacetime tests. Lean checks their actual time and momentum derivatives, their slice expectations, finite-sum linearity of the force action and integrability of the time-derivative expectation. The resulting weak equation is integral_[a,b] expectation_nu(t)(partial_t phi) dt plus J_[a,b](partial_p phi) equals expectation_nu(b)(phi(b,.)) minus expectation_nu(a)(phi(a,.)), for every ordered real interval and every finite tensor test in this class. Here J_[a,b] is half the difference of the two integrals against the restrictions of the same global positive-force measures. If each time factor vanishes at both endpoints the boundary expression is zero. The actual-model theorem constructs the SAME common semiclassical subsequence, weakly continuous all-real-time probability curve, compatible compactified force family and global force as before, now together with this time-dependent tensor weak equation. It retains the initial Dirac law, all-time characteristic limits, fixed-time weak probability convergence, exact canonical-window restrictions, extension uniqueness relative to that particular family, absolute continuity of both time marginals, absence of time atoms, C0 spacetime and projected momentum-force convergence on EVERY ordered real window, the original physical time budget and the Schwartz increment balance on all ordered real endpoints. The actual existence theorem retains fixed positive floor and width, strictly positive matter coefficients, an admissible nonzero hbar sequence tending to zero and any positive diverging resolvent scale. No extra physical evolution, limit-existence, differentiability-of-the-probability-curve or force-closure hypothesis is introduced. Analytic test regularity is an explicit test-class condition. No tensor-density theorem or extension to all smooth spacetime tests is asserted. A closed classical force functional, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. Possible escaped momentum mass is retained at compactification boundaries; global positive-force tightness and absence of this mass are not assumed or proved. Global total force mass is not assumed finite. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 1001 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_time_dependent_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
