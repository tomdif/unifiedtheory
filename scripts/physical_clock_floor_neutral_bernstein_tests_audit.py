#!/usr/bin/env python3
"""Audit constructed C1 Bernstein tensor approximations for localized Schwartz test curves.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_bernstein_tests_audit.py --overlay PATH

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


MODULES = [('KFCausalBernsteinPrimitive', 10), ('KFCausalBernsteinC1Approximation', 7), ('KFCausalCompactTimeLocalization', 8), ('KFCausalLocalizedBernsteinC1', 8), ('KFCausalMomentumPairTests', 6), ('KFCausalSchwartzCurveApproximation', 6)]


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
    logs = overlay/'physical-clock-floor-neutral-bernstein-tests-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_uniform_tests_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_bernstein_tests_audit.py']
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
        scope='A constructive C1 approximation argument is proved for real Banach-valued curves. The Bernstein basis is evaluated as an actual real polynomial on the whole real line. Integrating each basis polynomial from zero gives a scalar primitive with its proved derivative. A finite sum of these primitives times derivative snapshots, plus the initial value, defines the approximation. Its exact derivative is the Bernstein approximation of the sampled derivative, and its initial value is exact. The fundamental theorem of calculus expresses the value error as the integral of the derivative error. On the unit interval, the supremum value error is bounded by the supremum derivative error. Mathlib Bernstein uniform convergence therefore gives simultaneous uniform convergence of the value and derivative for a globally differentiable Banach-valued curve with continuous derivative. Compact time localization converts this into global bounded-continuous norm convergence. The cutoff consists of a bounded real C1 function with bounded continuous derivative and topological support contained in [0,1]. The derivative support is derived from the support of the cutoff. Weighted continuous curves are constructed as bounded continuous functions using compact support. A norm estimate proves that multiplication by the cutoff transfers interval convergence to global convergence. The product-rule derivative is tracked separately and also converges globally. The localized approximants are expressed as finite sums of explicit bounded C1 real scalar coefficients times the initial value and derivative samples; the scalar coefficients and their derivatives are constructed, and both finite-sum identities are proved. Pairing a bounded momentum function with its bounded momentum derivative supplies a real Banach space. Flattening a bounded time curve of such pairs into spacetime functions is a continuous linear map for each component. Complexifying the real time coefficients preserves their derivative identities. For Schwartz-valued time curves F and G, assume the bounded-continuous pair (F,F_p) has norm derivative (G,G_p) at every time and that the latter pair depends continuously on time. These are ANALYTIC TEST REGULARITY conditions, not assumptions on the physical probability curve or force. The construction gives explicit finite tensor tests with Schwartz coefficients equal to F(0) and finitely many G time samples. Their values, time derivatives and momentum derivatives are identified with the flattened Banach-valued approximants and converge in the global spacetime supremum norm. Thus the localized test chi(t)F(t,p), its actual time derivative chi_prime(t)F(t,p)+chi(t)G(t,p), and its momentum derivative chi(t)F_p(t,p) belong to the previously defined Approximable class by a constructed sequence, with no approximation-existence assumption for this class. The existing UniformWeakEquation consequently gives the weak equation and time integrability for these tests on every ordered real integration interval, including both probability boundary terms. The actual model already supplies UniformWeakEquation for its common subsequence, probability curve and global force; no model or operator or physical assumption is changed in this analytic extension. The cutoff construction in this audit is confined to the unit time window. Formal transfer to arbitrary time windows and a proof that every smooth compactly supported spacetime function supplies the required norm-differentiable Schwartz curve remain open. Therefore full spacetime-test density and the unrestricted smooth-test continuity equation are NOT claimed. Classical force identification, closed dynamics, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. Possible escaped momentum mass is retained; global positive-force tightness and absence of escaped mass remain unproved. The positive-floor clock obstruction persists. No necessity of a model change is established. All 1011 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_bernstein_tests_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
