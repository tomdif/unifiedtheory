#!/usr/bin/env python3
"""Audit graph cores and completed energy clock compositions.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_clock_core_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorShiftedResponseContraction', 5), ('KFCausalMultiplierPowerDecay', 3), ('KFCausalInvariantRangeCore', 6), ('KFCausalClockFloorDefectPowerDecay', 8), ('KFCausalClockFloorExponentialClockCore', 7), ('KFCausalClockFloorEnergyClockCore', 11)]


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
    logs = overlay/'physical-clock-floor-clock-core-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_clock_exponential_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_clock_core_audit.py']
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
        scope='For the existing equal-mobility clock-floor model with epsilon>0 and abs(hbar)<=2*pi*epsilon/3, the complex inverse gives a pointwise strictly contractive shifted response: abs(1-Bsymbol)<1. No uniform gap below one is assumed. Dominated convergence proves strong decay of powers of both I-D and I-B on all physical L2 states, where D=epsilon/C and B is the actual shifted defect. The same decay holds for the simultaneous eight-component output residual I-outputAction, whose powers are contractive. A constructive invariant-subspace theorem uses finite geometric sums to show that the closure of P(K) equals the closure of K when P preserves K and (I-P)^n decays strongly there. Applied to the actual full-domain defect graph identities, this proves that Dom(E C)=D(Dom E) is a graph core of E=exp(L/2), and Dom(T C)=D(Dom T) is a graph core of the ordered exponential T=E C^(-1/2). The mapped graphs are proved to be exactly the actual graphs restricted to those forward composition domains. Explicit polynomial approximants converge in both state and operator output. For every choice of complex weights, the defect image of the natural weighted eight-factor joint graph has the same graph closure. With the actual energy weights, that closure is the existing completed energy operator graph, including vanishing weights. A natural weighted clock-composition approximating sequence is obtained for every completed energy graph pair. The completed energy operator K itself also has the graph core Dom(K C)=D(Dom K); its graph restriction is identified exactly and explicit polynomial approximants converge to every graph pair. On this completed forward composition domain the actual clock output Cf, the completed energy output K(Cf), and the physical clock output of every component of Kf are constructed. Their differences are zero for the clock and kinetic components and equal the previously constructed Delta multiplier on the three matter/exponential components, with component norm bound abs(hbar)*norm((Kf)_i). The statements allow hbar=0 and make no nonzero-weight assumption. For vanishing weights the natural graph means the weighted graph (c_i*f,g_i) in graph(T_i); it does not impose unweighted domains for inactive factors. The convergence is in the graph norm of E, T or K, not the Hamiltonian operator graph norm. No uniform approximation rate over states, small-hbar families, clock floors or time windows is asserted. The results do not prove equality with the full reverse composition domains, a core for canonical clock momentum, a canonical P/E commutator, a charge-averaged form core, or the required Hamiltonian response and evolving-state bounds. Quantum clock-defect decay to zero, canonical clock-momentum tightness for the prescribed evolution, negative evolved longitudinal tails, continuous joint eleven-coordinate dynamics, force identification from the joint state, full phase-space transport, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. No model or Hamiltonian changed. All 1206 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_clock_core_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
