#!/usr/bin/env python3
"""Audit the full radial Hamiltonian response and actual expectation dynamics.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_radial_full_response_audit.py --overlay PATH

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


MODULES = [('KFCausalUnitaryMultiplierPairing', 2), ('KFCausalNeutralPositionRadialAdjoint', 3), ('KFCausalMixedRadialStripReflection', 3), ('KFCausalBoundedStripDifference', 4), ('KFCausalNeutralPositionRadialShiftPairing', 7), ('KFCausalNeutralPositionRadialOutputPairing', 6), ('KFCausalNeutralPositionRadialFullResponse', 6), ('KFCausalNeutralPositionRadialHamiltonianPairing', 2), ('KFCausalNeutralPositionRadialReferenceResponse', 3), ('KFCausalNeutralPositionRadialEhrenfest', 4), ('KFCausalNeutralPositionRadialResponseWindow', 3)]


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
    logs = overlay/'physical-clock-floor-radial-full-response-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_radial_full_form_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_radial_full_response_audit.py']
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
        scope='The original charge-compatible radial neutral-position observable now has a full hbar-normalized response estimate for the existing averaged Hamiltonian, and exact expectation dynamics along its actual unbounded propagator. Its adjoint is the same observable with reversed neutral frequency. Reflection of the actual complex clock inverse proves Q_v(y)^*=Q_-v(-y) for the constructed shifted operators. Cauchy estimates on the proved analytic strip give norm((Q_v(-hbar/2)-Q_v(hbar/2))f)<=abs(hbar)*D*norm(f), where d=pi*epsilon/3, M=exp(v^2*d^2/(2*delta*epsilon^2)), and D=2*M/d, for positive epsilon and delta and abs(hbar)<=d. All five clock/kinetic output rows cancel by adjoint duality; the final three matter rows have this difference bound. The bound passes through the actual circle average. For the existing completed form, physical embedding J, energy output A, radial actions F_v and F_-v, the full response C(u,w)=inner(Au,A(F_v w))-inner(A(F_-v u),Aw) satisfies norm(C(u,w))/abs(hbar)<=D*norm(Au)*norm(Aw)+c*(norm(Au)*norm(Jw)+norm(Ju)*norm(Aw)), where c=sqrt(1/2)*(4*sqrt(delta)+abs(v))/sqrt(epsilon). This includes every energy row and zero matter weights. On the existing Hamiltonian operator domain it equals inner(Hx,P_v y)-inner(P_-v x,Hy); no operator-domain preservation for P is assumed. The reference-form rate is i/hbar times that full response. The previously constructed weak equation and strong form continuity, together with the derived form lifts for P and its adjoint, now prove the exact complex expectation derivative, continuity of its rate, and the integral identity along the actual unbounded evolution for every reference-form initial state. Its rate is bounded by D*E(t)+2*c*norm(initial state)*sqrt(E(t)), where E is the actual time-dependent energy. For the existing normalized boosted states, fixed positive epsilon and initial clock width, nonnegative matter couplings and any admissible nonzero hbar sequence tending to zero, the existing energy theorem supplies an eventual finite-window rate and expectation Lipschitz bound: rate<=D*B_T+2*c*sqrt(B_T), and expectation difference<=that constant*abs(time difference), B_T=exp(2*T)*initialBudget. The eventual index is independent of radial cutoff and neutral frequency, though the displayed bound depends on them. Small-half-strip admissibility is derived eventually from hbar convergence rather than added as a sequence hypothesis. This closes the fixed-positive-regulator full response and time-variation steps. It does not prove neutral-position tightness, energy graph-norm cutoff removal, or an unregulated response limit. D is not uniform as delta or epsilon vanishes and does not vanish jointly with delta and v; L2 cutoff removal alone cannot pass the differentiated response. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect recovery, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and physical model are unchanged; no necessity of a model change is established. All 1115 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_radial_full_response_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
