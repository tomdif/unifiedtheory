#!/usr/bin/env python3
"""Recompile and audit full eight-factor and closed unaveraged form-domain clock-defect control.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_energy_defect_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seven new modules in dependency
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
    ('KFCausalClockFloorShiftedDefectPhysical', 9),
    ('KFCausalClockFloorMatterDefect', 5),
    ('KFCausalDirectionalTranslationMomentum', 11),
    ('KFCausalClockFloorKineticDefect', 6),
    ('KFCausalClockFloorEnergyDefectAction', 6),
    ('KFCausalClockFloorClosedEnergyDefect', 8),
    ('KFCausalClockFloorFormDefect', 7),
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
    logs = overlay/'physical-clock-floor-energy-defect-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_defect_full_domain_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_energy_defect_audit.py']
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
        scope='For the optional equal-mobility clock-floor model at epsilon>0 and abs(hbar)<=2*pi*epsilon/3, proved full natural-domain clock-defect control for all eight unaveraged physical energy factors and their actual simultaneous graph closure. The existing shifted defect B is proved equal to physical multiplication by complexDefect epsilon (chart epsilon s-i*hbar/2); this representative is derived through the actual weighted straightening unitary. Its norm is at most two. B preserves the full natural graphs of physicalField and fieldSquare and commutes with their values. Combined with the preceding full ordered identity T*D=B*T for T=exp(L/2)*C^(-1/2), this proves the actual matter identities (physicalField*T)*D=B*(physicalField*T) and (fieldSquare*T)*D=B*(fieldSquare*T), including every required unbounded multiplication domain. The matter factors are not asserted to commute with D. Independently constructed strongly continuous directional translations on arbitrary finite-dimensional Euclidean L2, identified their nonzero-hbar strong momentum with the actual maximal Fourier multiplier, and proved full graph preservation by every bounded operator commuting with these translations. Applied this to the physical clock defect D, which is constant along transverse translations, to prove transverseMomentum*D=D*transverseMomentum on the entire natural domain; a separate exact zero-symbol argument includes hbar=0. The actual clockHalf and inverse-clock-dressed clockMomentum graphs also commute with D. Thus D preserves the intersection of all eight natural energy-factor domains. Constructed a bounded action R on the eight-component energy output: D on the first five clock/kinetic components and B on the last three matter/exponential components. Its norm is bounded by two and hbar*Im inner(g,R^2*g)>=0 for every output vector g. For arbitrary finite energy weights, the natural joint graph is invariant under (f,g)->(D*f,R*g); continuous closure proves invariance of the entire existing closedEnergy graph, without assuming that the intersection of individual closed domains equals the joint closure. Vanishing weights impose no spurious domain restrictions. Consequently D and D^2 preserve the full closed unaveraged energy domain, the exact output is R times the previous output, and norm(E*D*f)<=2*norm(E*f). The actual complete unaveraged FormSpace carries a constructed bounded linear defect map with norm at most two, correct physical embedding, correct energy output, and the nonnegative signed squared-defect form pairing on every form vector. For every vector f in the actual representing unaveraged Hamiltonian domain, proved hbar*Im inner(H*f,D^2*f)>=0. This pairing does not assert that D preserves the Hamiltonian operator domain. No nonzero-hbar or additional Gaussian width assumption is needed for these physical energy identities. Charge-circle commutation of D, transfer to the full charge-averaged form, and a justified derivative or integrated expectation inequality along the actual averaged evolution remain open. No monotonic defect or common-time small-defect control under that evolution is claimed. The canonical clock commutator, controlled quantum-to-classical and finite-capacity limits, GR/QFT/Standard Model recovery and empirical identification remain unproved. All 519 predecessor source hashes, the physical model and the previously chosen operators are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_energy_defect_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
