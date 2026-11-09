#!/usr/bin/env python3
"""Audit longitudinal absorption of the actual matter derivative correction.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/matter_longitudinal_absorption_audit.py --overlay PATH

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


MODULES = [('KFCausalShiftedResponseComparison', 5), ('KFCausalTwoEndpointCorrection', 5), ('KFCausalLongitudinalResponseCoercivity', 3), ('KFCausalMatterAbsorptionWeight', 6), ('KFCausalMatterScalarAbsorption', 3), ('KFCausalMatterLongitudinalAbsorption', 3), ('KFCausalActualMatterAbsorbedLower', 2)]


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
    logs = overlay/'matter-longitudinal-absorption-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/matter_correction_quadratic_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/matter_longitudinal_absorption_audit.py']
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
        scope='With K=exp(pi/3), the actual complex clock and real clock satisfy the new response comparison on the existing closed strip. The real defect correction obeys abs(D-Re Z)<=(20*K*hbar^2/epsilon^2)*D^3*(1-D). The actual longitudinal coefficient obeys Re[Z*(1-Z)]>=(1/(2*K^2))*D*(1-D). A pointwise perfect square, without division by D or 1-D, absorbs the real correction into that longitudinal coefficient. The bounded nonnegative multiplication form H(f)=integral D^5*(1-D)*norm(f(x))^2 is constructed, continuous, and between zero and norm(f)^2; its density is integrable. For any two real multipliers of the same arbitrary complex L2 wavefunction, the actual derivative correction E satisfies abs(E)<=L(u)+beta*H(d), with beta=800*K^4*hbar^4/epsilon^5 and L the actual positive longitudinal response. The physical linear and quadratic field factors satisfy the common-wavefunction condition, retaining interference. The actual coherent matter response equals L+Q-E and is at least Q-beta*H(d), with all field, derivative and shear graphs retained. For actual continuous charge orbits, H(d(theta)) is integrable, abs(correctionMean)<=longitudinalMean+beta*integral H(d(theta)), and each actual matter rate is at least weightedMean-beta*integral H(d(theta)). The derivative outputs and their integrability are derived, with no new initial-state moment premise. This removes the separate unweighted matter-factor moment from the previous lower-bound remainder. The weighted shear and the remaining weighted derivative moment still have no sufficient bound by full Hamiltonian energy. The new estimate is a structural absorption result, not a uniformly smaller numerical bound throughout the admissible parameters. The hbar^4 coefficient alone implies neither a semiclassical limit for varying states nor regulator removal; it contains epsilon^(-5). The coherent response retains epsilon>0, a>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths. No Hamiltonian change is made. Common Hamiltonian form-core regularity, operator-domain membership, evolution invariance, the actual momentum evolution identity, long-time quantum clock recovery, controlled limits and physical Standard Model/Einstein identification remain open. No model change is established and the physical TOE remains unproved. All 1436 predecessor source/script hashes are preserved.')


    target = root/'data/matter_longitudinal_absorption_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
