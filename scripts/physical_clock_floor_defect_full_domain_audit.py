#!/usr/bin/env python3
"""Recompile and audit the full-domain clock-defect identities from a proved Gaussian graph core.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_defect_full_domain_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eight new modules in dependency
order, checks their printed axioms, checks the root import, and preserves the
preceding source hash chain. It is a scoped formal audit, not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [
    ('KFCausalMultiplierGraphCoordinates', 13),
    ('KFCausalModulatedGraphCore', 4),
    ('KFCausalEuclideanGaussianCore', 10),
    ('KFCausalGaussianStrip', 12),
    ('KFCausalClockFloorGaussianCore', 3),
    ('KFCausalClockFloorGaussianGraph', 6),
    ('KFCausalClockFloorDefectFullDomain', 10),
    ('KFCausalClockFloorOrderedDefectFullDomain', 6),
]


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
    logs = overlay/'physical-clock-floor-defect-full-domain-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_defect_sign_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_defect_full_domain_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proved a Gaussian graph core of the entire actual longitudinal half-exponential A=exp(L/2), for every epsilon>0 and real hbar. The proof constructs bounded coordinates that map all ordinary L2 onto the full graph of any measurable real multiplication operator. Fourier modulations of a pointwise nonvanishing weight w with both w and m*w in L2 are then proved graph-dense using the existing ordinary L2 totality theorem. Explicit self-Fourier Euclidean Gaussians satisfy the exponential weighted integrability for every real hbar. Transport through the existing physical Fourier unitary yields equality of the closed span of the new Gaussian packet graph pairs with the entire original A graph; graph density is not assumed and the operator is not replaced. Translated Gaussians with bounded analytic clock multipliers have explicit L1 and L2 strip estimates. The contour shift and full six-dimensional Fourier integral prove actual A graph pairs, with exact identification of the unmultiplied input with this Gaussian core. For epsilon>0 and abs(hbar)<=2*pi*epsilon/3, applying the analytic defect and the existing bounded shifted defect B to the two components preserves the actual A graph on every Gaussian generator. Closedness and the proved core extend this to EVERY pair (f,g) in the natural A graph: (D*f,B*g) and (D^2*f,B^2*g) are in that same graph. Thus D preserves the entire A domain and A*D*f=B*A*f holds there with explicit domain witnesses. The existing quadratic commutator bound and hbar*Im inner(g,B^2*g)>=0 now apply to these full-domain graph pairs. Since the actual bounded inverse half-clock S commutes with D, the same exact identity T*D*f=B*T*f holds on the entire natural domain of T=A*S, without a restricted coherent-subgraph hypothesis. Proved full ordered-domain preservation by D and D^2, norm(T*D*f-D*T*f)<=(2*abs(hbar)/epsilon)*norm(D^2*T*f), and hbar*Im inner(T*f,T*D^2*f)>=0 using actual operator applications and checked domains. These results do not require hbar nonzero or the older coherent width restriction; the strip inequality remains a sufficient condition for the defect transfer, not a proved necessary condition. The new Gaussian core is auxiliary: no membership of these Gaussians in all common physical energy-factor domains or equality with the old sheared coherent subgraph is asserted. Weighted intertwining for physicalField*A*S and fieldSquare*A*S, full averaged form-domain preservation, a justified expectation derivative and monotonic defect along the actual full Hamiltonian evolution remain unproved. The canonical clock commutator, common-time small-defect control, controlled quantum-to-classical and finite-capacity limits, GR/QFT/Standard Model recovery and empirical identification remain open. All 510 predecessor source hashes and the physical model are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_defect_full_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
