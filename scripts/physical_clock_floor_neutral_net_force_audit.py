#!/usr/bin/env python3
"""Audit Fourier reconstruction and conditional global net-force uniqueness.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_net_force_audit.py --overlay PATH

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


MODULES = [('KFCausalForceFourierSeparation', 8), ('KFCausalNetForceUniqueness', 5), ('KFCausalSpacetimeMeasureSeparation', 4), ('KFCausalGlobalNetForceUniqueness', 6), ('KFCausalForceFourierReconstruction', 5), ('KFCausalNeutralNetForceDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-net-force-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_smooth_tests_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_net_force_audit.py']
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
        scope='The finite net force on one real momentum dimension is uniquely determined by its action on derivatives of Schwartz functions. Characteristic functions of finite positive measures are proved continuous using Fourier-integral continuity. The force Fourier transform is the half-difference of the two characteristic functions and is continuous. Fourier pairing converts equality of all derivative-test actions into vanishing integrals of a continuous Fourier multiplier against every Schwartz function. Smooth compact real test functions are embedded into the complex Schwartz space. The fundamental lemma for smooth compact test integrals gives almost-everywhere vanishing, and continuity upgrades it to everywhere vanishing. Away from zero frequency the nonzero Fourier derivative multiplier can be cancelled; continuity on the dense complement of zero fixes the remaining frequency. Equality of the force Fourier transforms then gives the cross-sum measure identity F.positive+G.negative=G.positive+F.negative by characteristic-function injectivity for finite positive measures. This identity implies equality of force actions on every bounded continuous momentum test. In particular, any two finite force pairs satisfying the same interval Schwartz balance for the same endpoint measures are net-equivalent. No uniqueness of the positive decomposition is claimed. A general measure-separation theorem proves that spacetime measures finite on every bounded time window are determined by all rectangles Icc(a,b) times measurable momentum sets. The proof first separates finite measures by time-section pushforwards and finite-product measure extensionality, then exhausts the real time axis by bounded windows. This does not assume globally finite total mass or incorrectly use finite-product extensionality directly on arbitrary sigma-finite measures. Applying the finite net-force uniqueness on every ordered real interval gives global cross-sum equality J.positive+K.negative=K.positive+J.negative whenever J and K obey the interval balance for the SAME neutral momentum probability curve. Consequently all bounded continuous spacetime force actions agree on every time window. The competing force need not come from the same compactified positive/negative window family or extraction. This is uniqueness of the NET flux conditional on the entire probability curve, not uniqueness of that curve or of the positive/negative decomposition. A second Fourier-duality argument reconstructs the finite integrated net force from the endpoint laws: i*v*J_[a,b].fourier(v)=charFun(nu_b)(v)-charFun(nu_a)(v) at every real frequency; for v nonzero the force transform is the endpoint difference divided by i*v. Continuity fixes zero frequency, without division by zero. The reconstruction and global conditional uniqueness are attached to the actual-model existence theorem while retaining the SAME common semiclassical subsequence, continuous neutral momentum probability curve, initial Dirac law, characteristic-function and fixed-time probability limits, compactified force-window limits, global positive/negative force measures with exact window restrictions, earlier relative uniqueness, time absolute continuity, absence of time atoms, all ordered real C0 force-action limits, physical time marginal budget, interval Schwartz balance, TensorWeakEquation, UniformWeakEquation and full SmoothWeakEquation. No new physical assumptions are added. The preceding positive floor and width, positive matter coefficients, admissible nonzero hbar sequence tending to zero and positive resolvent scale tending to infinity remain required. No model or operator is changed. This removes an independent net-force extraction ambiguity once the probability curve is fixed. It does NOT identify a classical force as a local functional of the evolving physical state, close the evolution law, prove uniqueness of the probability curve across semiclassical subsequences or establish full phase-space dynamics. Remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. Possible escaped positive/negative momentum mass is retained; global positive-force tightness and absence of escaped mass remain unproved. The positive-floor clock obstruction persists. No necessity of a model change is established. All 1027 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_net_force_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
