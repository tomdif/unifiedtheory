#!/usr/bin/env python3
"""Recompile and audit the signed defect pairing and its extension to closed ordered subgraphs.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_defect_sign_audit.py --overlay PATH

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
    ('KFCausalClockFloorDefectSign', 7),
    ('KFCausalClockFloorShiftedDefect', 8),
    ('KFCausalSignedMultiplierPairing', 1),
    ('KFCausalClockFloorShiftedDefectBounds', 4),
    ('KFCausalClockFloorDefectGraphClosure', 6),
    ('KFCausalClockFloorBoundedInverse', 6),
    ('KFCausalClockFloorOrderedDefectClosure', 4),
    ('KFCausalClockFloorOrderedDefectTrial', 3),
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
    logs = overlay/'physical-clock-floor-defect-sign-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_defect_commutator_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_defect_sign_audit.py']
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
        scope='For the optional equal-mobility clock-floor model at epsilon>0, proved that the real part of the analytic complex clock is positive and the imaginary part has the same sign as the target clock imaginary part. The analytic defect has nonnegative real part and the opposite imaginary sign. Therefore hbar*Im(D(q-i*hbar/2)^2)>=0 under the current abs(hbar)<=2*pi*epsilon/3 sufficient strip condition. Constructed the actual bounded shifted-defect operator B on all physical L2 by conjugating its verified complex multiplier through the existing straightening unitary. On every physical L2 vector g, norm(B g)<=2*norm(D g), norm(B g-D g)<=(2*abs(hbar)/epsilon)*norm(D^2 g), and norm(B^2 g-D^2 g)<=(6*abs(hbar)/epsilon)*norm(D^3 g). A general L2 integral theorem transfers the scalar imaginary sign to hbar*Im inner(g,B^2 g)>=0 for every g. No exponential-domain assertion follows merely from boundedness of B. For positive Gaussian widths a,alpha,beta with 32*beta<=alpha, formed the closed linear span of the actual exp(L/2) graph pairs indexed by real clock modulation, arbitrary complex transverse sources and finite defect powers. This subspace is proved to lie in the actual closed exponential graph and to be invariant under (f,g)->(D f,B g). Consequently the actual domain-checked identities A D f=B A f and A D^2 f=B^2 A f, the commutator bound and the signed form pairing extend to coherent finite superpositions and their graph-norm limits. Equality of this subgraph with the entire A graph is not assumed or proved. Independently constructed the actual bounded inverse half-clock S=C^(-1/2), proved norm(S f)<=epsilon^(-1/2)*norm(f), exact equality to the existing inverseAction and inverseClockHalf graph, and commutation S D=D S. The existing natural ordered exponential T=A S is proved closed for every real hbar at epsilon>0, since its graph is the continuous preimage of the closed A graph; no new operator extension is chosen. Pulling back the constructed coherent subgraph by (f,g)->(S f,g) gives a closed subgraph of this same T. It is D-invariant and carries the actual ordered graph pairs for f,D f,D^2 f, the commutator estimate and hbar*Im inner(T f,T D^2 f)>=0. The existing nonzero charge-zero physical trial, already in all eight common energy-factor domains, is explicitly identified with a member of this ordered subgraph through its inverse-damped Gaussian. The new subgraph is therefore not merely a vacuous interface. No graph-core equality, form-norm density or preservation by the full averaged Hamiltonian is proved. The matter factors include physicalField*A*S and fieldSquare*A*S, so they cannot simply be treated as commuting with D; their weighted intertwining and full-domain transfer still need proof. Converting the sign to monotonic squared defect along the actual weak evolution also requires form-domain invariance and a justified expectation derivative. No monotonicity or prescribed common-time small-defect bound is claimed. The older density-constructed normalized small-defect family has not been identified with quantitative analytic packets. The canonical clock commutator, controlled quantum-to-classical and finite-capacity limits, GR/QFT/Standard Model recovery and empirical identification remain open. All 501 predecessor source hashes and the older model are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_defect_sign_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
