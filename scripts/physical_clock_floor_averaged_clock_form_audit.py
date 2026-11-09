#!/usr/bin/env python3
"""Audit charge-averaged clock cores and the actual Hamiltonian weak clock form.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_averaged_clock_form_audit.py --overlay PATH

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


MODULES = [('KFCausalLpStrongPowerDecay', 6), ('KFCausalEmbeddedResponseDecay', 4), ('KFCausalClockFloorAveragedResponseDecay', 8), ('KFCausalEmbeddedClockCore', 3), ('KFCausalClockFloorAveragedClockCore', 10), ('KFCausalClockFloorClockOutputForm', 9), ('KFCausalClockFloorAveragedClockResponse', 7), ('KFCausalClockFloorAveragedHamiltonianClockForm', 4)]


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
    logs = overlay/'physical-clock-floor-averaged-clock-form-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_clock_core_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_clock_form_audit.py']
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
        scope='For the existing clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, this audit derives the full charge-averaged clock form core and a continuous Hamiltonian clock-response form. A generic dominated-convergence argument lifts contractive strong power decay to vector-valued L2 for an arbitrary measure. A separate embedding theorem transfers decay and contractivity through the exact form-norm identity. On the actual averaged form space the residual of formAction is contractive and its iterates tend strongly to zero; this is auxiliary approximation, not quantum time evolution. The range of formAction is proved to be exactly the form vectors whose actual clock output is again represented by a form vector. This range is dense in the full averaged form norm, with explicit finite-geometric-sum approximants. The actual averaged energy graph is characterized by its form representatives. Its defect image is exactly its restriction to D(Dom K)=Dom(K C), and that restriction is a graph core of the actual charge-averaged energy operator K. Explicit approximants converge in both physical state and averaged energy output. Here C is multiplication by exp(s)+epsilon and D=epsilon/C. The bounded diagonal output correction Delta contains the previous factorDifference, zero in the first five components and the actual clock shift difference in the last three. Its norm on both the eight-component output and its charge-angle L2 lift is bounded by abs(hbar) times the input norm. Actual C graph pairings are symmetric; actual clock outputs of the energy components are constructed on the form clock domain. Consequently inner(Kf,K(Cg))-inner(K(Cf),Kg) equals inner(Delta Kf,Kg)-inner(Kf,Delta Kg) there. The right side defines a continuous sesquilinear response on the entire averaged form space, bounded by 2*abs(hbar)*norm(Kf)*norm(Kg). It is the unique continuous extension agreeing with all actual core clock pairings. The existing Hamiltonian form representation then identifies this response with inner(Hf,Cg)-inner(Cf,Hg) whenever f,g lie in the actual averaged Hamiltonian domain and Cf,Cg lie in the averaged form domain. This is a weak form identity with the stated graph-domain premises; it neither assumes nor proves existence of H(Cf) or C(Hf), invariance of the Hamiltonian domain, a Hamiltonian operator graph core, or density of the Hamiltonian/clock common operator domain. The form identity and its continuous extension are unconditional for the actual model parameters, and no nonzero-weight or charge-zero restriction is imposed. No uniform approximation rate in state, hbar, epsilon or physical time is asserted. No evolving-state Ehrenfest law for the unbounded C, canonical clock-momentum/exponential commutator, canonical momentum tightness, negative evolved longitudinal tails, or quantum clock-defect decay is proved here. Continuous joint eleven-coordinate dynamics, force identification from the joint state, full phase-space transport, regulator removal, GR/QFT/Standard Model identification and empirical validation remain open. No model or Hamiltonian changed. All 1213 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_clock_form_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
