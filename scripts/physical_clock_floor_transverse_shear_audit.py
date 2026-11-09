#!/usr/bin/env python3
"""Audit the actual transverse shear momentum and its clock-operator relations.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_transverse_shear_audit.py --overlay PATH

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


MODULES = [('KFCausalTransverseShearCoordinates', 8), ('KFCausalTransverseShearTransport', 10), ('KFCausalStrongUnitaryProductDerivative', 3), ('KFCausalTransverseShearClockCommutation', 9), ('KFCausalTransverseShearMomentum', 9), ('KFCausalTransverseShearDifferential', 7), ('KFCausalTransverseShearGraphCommutation', 10), ('KFCausalClockFloorShearCommonDomain', 1)]


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
    logs = overlay/'physical-clock-floor-transverse-shear-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_pure_clock_charge_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_transverse_shear_audit.py']
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
        scope='For the existing model this audit constructs the actual transverse shear unitary and selfadjoint momentum J, without changing the model or Hamiltonian. The relative coordinate unitary V=Uc U0^-1 is proved to have the all-L2 representative exp(-s)*f(s,flow(-s)y), independent of every positive clock floor. The constructed S(t)=V tau(t) V^-1 tau(-t) has representative exp(t)*f(s,flow(t)y): it fixes the clock. Null-set preservation, group composition, unitarity and strong continuity are proved. The actual maximal strong generator J=-i*hbar*dS/dt is densely defined, selfadjoint and closed for nonzero hbar, with an orbit-average graph core. A general strong-unitary product derivative rule uses strong continuity, without operator-norm differentiability. It derives the actual graph Jf=V P V^-1 f-Pf when both canonical domains hold; this is not a maximal sum-domain equality. For every C1 compact physical function, membership in both canonical domains and hence Dom(J) is derived, using the explicit inverse chart and preservation of C1 compact support. Pointwise and strong L2 derivatives identify the actual J graph output as -i*hbar*(fderiv(f)(0,velocity(y))+f). The density correction is retained. Shear commutes on all L2 states with the actual pure and coupled coordinate unitaries, their inverses, canonical clock translation, both pure and coupled clock transports, and bounded clock multipliers. In particular it commutes with D=epsilon/C and R=C^(-1/2). Differentiation proves preservation in both directions of the full maximal B and L graphs by S, and of the full J graph by the pure and coupled clock transports. D and R preserve the full J graph with exactly commuting outputs. Every C1 compact physical state has actual P, B, L and J graph outputs satisfying Lf=Bf+C^(-1)Jf, with norm(Bf)<=norm(Lf)+norm(Jf)/epsilon. The common-domain comparison requires epsilon>0 and hbar!=0, without a small-hbar restriction. The shear unitary itself has no floor or hbar parameter. No compact-state graph core for B or J, maximal sum-domain identity, or generic compact-state membership in the vacuum exponential domain is claimed. Strong commutation with L transport does not in this audit supply the required graph commutation with its unbounded exponential or the ordered vacuum factor T=exp(L/2)R. Those domain/commutation results, a common vacuum/shear/clock core, charge-averaged shear force control, the full Hamiltonian momentum response and cutoff removal remain open. No bound for J or B along Hamiltonian evolution is proved. Quantum clock escape, evolved canonical momentum tightness, closed joint phase-space dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. All 1275 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_transverse_shear_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
