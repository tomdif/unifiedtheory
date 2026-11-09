#!/usr/bin/env python3
"""Audit the constructed selfadjoint pure-clock momentum and actual domain identities.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_pure_clock_momentum_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorPureClockCoordinates', 8), ('KFCausalClockFloorPureClockLpCoordinates', 16), ('KFCausalClockFloorPureClockTransport', 19), ('KFCausalClockFloorPureClockMomentum', 14), ('KFCausalClockFloorPureClockDerivative', 7), ('KFCausalClockFloorPureClockDifferential', 7), ('KFCausalClockFloorPureClockSandwich', 8), ('KFCausalClockFloorPureClockCommonDomain', 5), ('KFCausalClockFloorPureClockDefectMomentum', 7)]


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
    logs = overlay/'physical-clock-floor-pure-clock-momentum-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_vacuum_momentum_form_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_pure_clock_momentum_audit.py']
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
        scope='For the unchanged clock-floor model with epsilon>0, this audit constructs a unitary coordinate map acting only on the physical clock: U0 f(s,y)=sqrt(exp(s)+epsilon)*f(exp(s)+epsilon*s,y). Its norm identity is proved by the actual clock change of variables, extended from dense compact continuous tests, and identified on all L2 states with inverse representatives and null-set preservation. Conjugating canonical translation gives an actual strongly continuous unitary group with physical flow (logFlow(s,t),y) and half-density sqrt(C(s)/C(logFlow(s,t))). All transverse coordinates remain fixed. Its momentum B is densely defined, closed and selfadjoint for every nonzero hbar; no small-hbar condition is required for these new results. The full maximal domain is strong differentiability of this actual group. Its graph is unitarily conjugate to the canonical clock-momentum graph, with an exact Fourier multiplier characterization and a constructed orbit-average graph core. The physical differential expression is Bf=-i*hbar*(C^-1*partial_s f-exp(s)/(2*C^2)*f), established in the actual maximal graph whenever the displayed function and differential are L2. Every C1 compactly supported state satisfies all these L2 conditions. On each such state, R=C^-1/2 gives actual Rf in Dom(P), actual Bf, and R(P(Rf))=Bf. This is an actual composition-domain identity, not an assumed maximal-domain equality for the unclosed sandwich RPR. Canonical, pure-clock and coupled longitudinal momenta are compared on the same compact states with all outputs derived: Bf=C^-1*Pf+r, Lf=Bf+d, r=i*hbar*exp(s)/(2*C^2)*f, and d=C^-1*(-i*hbar)*(transverse directional derivative of f+f). The uniform coefficient estimate exp(s)/(2*C^2)<=1/(8*epsilon) proves norm(r)<=abs(hbar)/(8*epsilon)*norm(f) and norm(Bf)<=norm(Pf)/epsilon+abs(hbar)/(8*epsilon)*norm(f). No shear-output evolution bound is assumed. The actual defect D=epsilon/C preserves the full maximal domain of B, with [B,D]f=(i*hbar/epsilon)*D^2*(1-D)*f, proved by the new transport intertwining and the previously audited scalar/operator derivative. These are observable construction and domain results, not Hamiltonian evolution or a model change. The orbit-average core is for B; compact states have not been proved to be a graph core here, and equality of the maximal B domain with the unclosed RPR composition domain is not asserted. Charge invariance of B, its commutator with the ordered vacuum factor, kinetic/matter responses, charge-averaged force estimates, cutoff removal for a B evolution law, and long-time quantum clock escape remain open. The prior positive longitudinal vacuum response cannot be transferred to B by dropping its shear difference. Canonical momentum control, closed joint dynamics, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. All 1257 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_pure_clock_momentum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
