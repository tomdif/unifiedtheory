#!/usr/bin/env python3
"""Audit actual pure-clock responses of clock and kinetic factors.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_pure_clock_factors_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorPureClockInverseHalf', 5), ('KFCausalClockFloorPureClockFields', 6), ('KFCausalClockFloorPureClockTransverse', 9), ('KFCausalClockFloorPureClockKinetic', 6), ('KFCausalClockFloorPureClockKineticCore', 4), ('KFCausalClockFloorPureClockKineticResponse', 13), ('KFCausalClockFloorPureClockClockResponse', 14)]


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
    logs = overlay/'physical-clock-floor-pure-clock-factors-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_pure_clock_vacuum_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_pure_clock_factors_audit.py']
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
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (root/source).read_text()), source
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
        scope='For the existing clock-floor candidate, actual pure-clock transport commutes with all physical transverse translations. Consequently each maximal transverse momentum graph, the physical linear-field graph, and the field-square graph are preserved by that unitary group. Closed-operator orbit averaging constructs separate graph cores with pure-clock momentum on input and output, and yields exact momentum-composition interchange. The bounded inverse half-clock R=C^(-1/2) preserves the entire actual B momentum domain, with [B,R]f=(i*hbar/(2*epsilon))*D*(1-D)*R f, where D=epsilon/C. For the original kinetic factor K=P_v R, if Kf=g and Bf=b, then Kb=k if and only if Bg=k+(i*hbar/(2*epsilon))*D*(1-D)*g. Thus the natural KB and BK composition domains agree on Dom(K) intersect Dom(B). A dense K graph core with B on input and output is constructed using the transverse core, the bounded map (R,(1/epsilon)D), R squared=(1/epsilon)D, and strong decay of defect residuals. Both compositions exist there. The unscaled weak response (-2/hbar) Im inner(Kf,K(Bf)) equals Rkin(Kf), where Rkin(g)=(1/epsilon) Re inner(g,D*(1-D)g), and 0<=Rkin(g)<=norm(g)^2/(4*epsilon). The kinetic commutator norm is at most abs(hbar)*norm(Kf)/(8*epsilon). This quadratic response extends uniquely and continuously from the constructed core to the full K graph, with explicit convergent core approximants. For the clock-half factor A=C^(1/2), the bounded map g -> (R g,g) and density of Dom(B) construct its graph core with both AB and BA compositions. On that core [B,A]f=-(i*hbar/(2*epsilon))*D*(1-D)*Af. Its unscaled weak response is -Rkin(Af), extends uniquely across the entire A graph, and equals -Re inner(f,(1-D)f), hence lies between -norm(f)^2 and zero. Clock composition outputs are constructed when Af belongs to Dom(B); an unrestricted reverse composition-domain theorem for A is not asserted. All new momentum results require epsilon>0 and hbar!=0 without a small-hbar restriction. The graph core claims are separate for each factor, not a joint core for the eight-factor Hamiltonian or its charge average. Physical linear-field and field-square commutation with B does not itself establish responses of the ordered matter factors A*T. Vacuum weighted-shear control, matter responses, compatible full form domains, charge averaging of the full force, and a Hamiltonian evolution law with cutoff removal remain open. The actual Hamiltonian is time dependent with exp(2*t) coefficients; these factor bounds are not a conservation-of-energy argument or a uniform-in-time force bound. Quantum clock escape, evolved momentum tightness, closed joint dynamics, regulator removal and GR/QFT/Standard Model and empirical identification remain open. The model and Hamiltonian are unchanged. All 1300 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_pure_clock_factors_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
