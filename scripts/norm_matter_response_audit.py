#!/usr/bin/env python3
"""Audit the actual weighted-norm secant and its full matter response bounds.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/norm_matter_response_audit.py --overlay PATH

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


MODULES = [('KFCausalClockSecantRatio', 6), ('KFCausalClockSecantMultiplier', 10), ('KFCausalShearNormSecant', 3), ('KFCausalTransportedNormSecant', 3), ('KFCausalNormMatterAverage', 4), ('KFCausalNormMatterResponse', 2)]


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
    logs = overlay/'norm-matter-response-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/transported_matter_average_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/norm_matter_response_audit.py']
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
        declared = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected == declared, (name, expected, declared)
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
        scope='The actual inverse-clock strip implies abs(Im(epsilon/(exp(z)+epsilon)))<=abs(Im(z))/2. Consequently rho=w^2/Re(c), where w is the physical shear root and c is the actual interpolation coefficient, is continuous with 0<=rho<=epsilon/4 for both signs of nonzero hbar. The bounded real clock multiplier M=sqrt(rho) satisfies norm(Mf)^2<=epsilon/4*norm(f)^2. An explicit bounded real clock multiplier for rho*Im(c), together with preservation of the actual self-adjoint shear graph, proves Re inner(Mf,M Cj)=Re inner(Wf,Wj) whenever (f,j) is in the actual shear graph. Thus an unforced path Uprime=C J U has Nprime=2q, with N=norm(MU)^2 and q the physical weighted shear expectation. Monotonicity of q gives q_final >= (N_final-N_initial)/2 >= -epsilon/8*norm(U_initial)^2. The actual transported polynomial Gaussian paths supply all derivative, graph and monotonicity premises, including arbitrary finite complex superpositions and their interference. Their actual original endpoints and intrinsic initialInput identify the estimate on the coherent span. Both initial norm costs are continuous along charge rotations and integrable; the final weighted norm is integrable. Charge integration yields the norm secant and simpler initial-norm bound. Actual longitudinal absorption then gives each matter rate at least (2/epsilon^2)*(mean final weighted norm squared - mean initial weighted norm squared) - betaAbs*mean H(d_terminal), and also at least -mean norm(initialInput)^2/(2*epsilon) - betaAbs*mean H(d_terminal). Here betaAbs=800*exp(4*pi/3)*hbar^4/epsilon^5, H(d)=integral D^5*(1-D)*norm(d)^2, and the exact terminal derivative representative, continuity and moment integrability are derived. The full theorem constructs the actual momentum b=Bf, form lifts of f and b, all eight energy-factor outputs and derivative curves, identifies the full form pairing with the actual eight-factor rate, and carries both bounds to the full response with the mass/quartic weights, exp(2t) and the existing loss norm(f)^2/2. This removes the signed initial shear derivative from an alternative lower bound; no separate initial shear estimate, additional energy, force, sign or moment premise is assumed. The preceding signed-initial bound remains valid, and no universal comparison to it is asserted. Conditions remain epsilon>0, a>0, nonzero hbar, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths, including the strip boundary. Sufficient one-sided Hamiltonian-energy control of the combined initial norm cost and terminal derivative correction remains unproved. Initial field recipes are algebraic operators on the coherent span, not proved Hilbert-bounded or closable. There is no common Hamiltonian form-core result, evolution invariance, momentum evolution identity, long-time quantum clock recovery, controlled regulator limits, physical Standard Model/GR identification or octonion necessity. The auxiliary interpolation is not Hamiltonian time, and the actual energy is explicitly time dependent. No model change is established; the physical TOE remains unproved. All 1478 predecessor source/script hashes are preserved.')


    target = root/'data/norm_matter_response_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
