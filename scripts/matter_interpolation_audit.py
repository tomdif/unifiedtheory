#!/usr/bin/env python3
"""Audit the constructed field-weighted imaginary-shear interpolation.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/matter_interpolation_audit.py --overlay PATH

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


MODULES = [('KFCausalGaussianAllRadiusMoments', 5), ('KFCausalImaginaryShearCocoercivity', 3), ('KFCausalForcedShearVariation', 4), ('KFCausalFieldInterpolationBounds', 6), ('KFCausalPolynomialImaginaryShearCurve', 15), ('KFCausalActualPolynomialShearCurve', 10), ('KFCausalFieldShearPathGraphs', 11), ('KFCausalFieldShearInterpolationEstimate', 11), ('KFCausalCoherentMatterInterpolation', 4)]


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
    logs = overlay/'matter-interpolation-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/matter_longitudinal_absorption_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/matter_interpolation_audit.py']
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
        scope='The actual clock-chart strong-monotonicity theorem implies epsilon*norm(relativeShift)^2<=shiftImag*Im(relativeShift), hence 2*epsilon*norm(c)^2<=Re(c) for the actual imaginary-shear coefficient c=i*relativeShift/hbar, for either sign of nonzero hbar on the existing closed strip. Its bounded L2 multiplier C satisfies 2*epsilon*norm(C f)^2<=Re inner(f,C f). Completing a square yields -(hbar^2/(4*epsilon))*norm(d)^2<=2*Re inner(f,C(f+i*hbar*d)) for all L2 vectors. A graph/strong-derivative criterion identifies this as the lower bound on the variation of a field-weighted shear expectation; its analytic hypotheses are then derived for the actual interpolation. All polynomial radius moments of the Gaussian envelope are proved. Both field powers and their shear derivatives have derived polynomial bounds. Their weighted input and first-shear curves have derived strong L2 derivatives and continuous extensions to the closed interpolation interval; all required weighted second outputs are constructed. In these definitions weightedFirst means P*JG and does not silently mean J(PG). The actual field commutator constructs J(FG)=FJG-i*hbar*(v dot grad F)G throughout the path and derives its strong derivative using a second actual shear graph. The construction extends to finite complex Gaussian superpositions with cross terms retained. For every bounded clock multiplier W, the actual interpolation expectation q(tau)=Re inner(W F G_tau,W J(F G_tau)) satisfies qPrime>=-(hbar^2/(4*epsilon))*norm(W d_tau)^2 on the open unit interval, with d_tau=(v dot grad F)G_tau. Its cost is continuous and interval-integrable; monotonicity of q plus the accumulated cost gives q(1)>=q(0)-(hbar^2/(4*epsilon))*integral_0^1 norm(W d_tau)^2. The endpoint is identified with any actual ordered-exponential, field-power and shear graph outputs for every state in the existing coherent span. For the existing physical weight W=root, the actual weighted matter shear Q is bounded below by (4/epsilon^2)*q(0)-(hbar^2/epsilon^3)*integral_0^1 norm(W d_tau)^2. This is a constructed interpolation estimate, not an assumed evolution equation or a positivity theorem for weighted matter shear. The initial field-weighted expectation may be signed, and the path cost has no sufficient Hamiltonian-energy bound. Separate charge-angle continuity/integrability of these new endpoint/cost expressions has not been derived here; the new endpoint bound is pointwise in charge angle. Prior charge-average results retain their previous scope. No extra initial-state moment hypothesis or Hamiltonian change is introduced. Conditions remain epsilon>0, a>0, nonzero hbar, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths; the auxiliary Gaussian seed construction also states its positive widths and 32*beta<=alpha. Hamiltonian energy control, common form-core/evolution regularity, the actual momentum evolution identity, long-time quantum clock recovery, controlled limits and physical Standard Model/Einstein identification remain open. No model change is established and the physical TOE remains unproved. All 1444 predecessor source/script hashes are preserved.')


    target = root/'data/matter_interpolation_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
