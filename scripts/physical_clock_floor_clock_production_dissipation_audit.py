#!/usr/bin/env python3
"""Audit actual clock production and the global defect dissipation budget.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_clock_production_dissipation_audit.py --overlay PATH

Sequential direct Lean checks rebuild eleven new modules, audit their axioms,
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


MODULES = [('KFCausalClockFloorClockVelocity', 10), ('KFCausalClockFloorClockProduction', 11), ('KFCausalClockFloorClockOutputProduction', 9), ('KFCausalClockFloorAveragedClockProduction', 10), ('KFCausalClockFloorStrictClockProduction', 3), ('KFCausalClockFloorClockVelocityApproximation', 1), ('KFCausalClockFloorClockProductionApproximation', 5), ('KFCausalClockFloorStrictClockGrowth', 12), ('KFCausalClockFloorDefectVelocityCoercivity', 5), ('KFCausalClockFloorDefectProductionCoercivity', 8), ('KFCausalClockFloorDefectDissipationBudget', 9)]


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
    logs = overlay/'physical-clock-floor-clock-production-dissipation-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_unbounded_clock_ehrenfest_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_clock_production_dissipation_audit.py']
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
        scope='For the existing clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, this audit proves clock growth and a global dissipation budget along the actual charge-averaged unitary propagator on its completed reference form domain. No model or Hamiltonian is changed. The actual complex shift gives a scalar quantum clock velocity between one half of rho and 1, where rho=exp(s)/(exp(s)+epsilon)=1-D and D=epsilon/(exp(s)+epsilon). The velocity is strictly positive. Its difference from rho is at most (2*abs(hbar)/epsilon)*D^2. These bounds are lifted through the actual physical L2 multipliers, the eight-component energy output and charge averaging. The exact unbounded-clock rate equals the derived real production form, is nonnegative, is at least one half of the explicit classical-response production form and is at most the instantaneous energy. With positive vacuum coupling k and nonzero physical initial vector, its rate is strictly positive and its clock expectation strictly increases for all real times. Faithfulness of the actual vacuum output is carried through charge averaging and completion; strict production is not assumed. The error between the quantum clock rate and the classical-response form evaluated on the same quantum state is bounded by (2*abs(hbar)/epsilon) times instantaneous energy, with corresponding initial-energy and finite-interval balance bounds. This is a comparison of forms on the actual quantum state, not identification of a classical probability evolution. A separate scalar estimate proves quantum defect dissipation at least one thirty-second of the nonnegative classical defect dissipation -drift(D). It uses the exact shifted-clock/defect identity and the bound norm(shiftedClock)<=4*C, and is lifted through the actual energy outputs and averaging. The exact defect Ehrenfest law therefore gives, for any a<=b, the integral of classical-response dissipation on [a,b] at most 32*(expectation(D)_a-expectation(D)_b), hence at most 32*expectation(D)_a. The latter bound is independent of the interval length. The dissipation is continuous and nonnegative, its average over [a,a+T] is bounded by 32*expectation(D)_a/T and tends to zero as T tends to infinity, and it is arbitrarily small at arbitrarily late times. These budget results require no positive vacuum-coupling assumption. Strict clock growth does not establish clock divergence, and vanishing average dissipation does not identify the limiting defect expectation as zero. No quantum long-time clock-defect recovery, evolving canonical clock-momentum tightness, closed joint eleven-coordinate dynamics, full phase-space transport, regulator removal, GR/QFT/Standard Model identification or empirical validation is proved. All 1234 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_clock_production_dissipation_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
