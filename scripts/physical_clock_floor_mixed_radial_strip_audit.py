#!/usr/bin/env python3
"""Audit the actual mixed clock coordinates and analytic radial multiplier.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_mixed_radial_strip_audit.py --overlay PATH

Sequential direct Lean checks rebuild fourteen new modules, audit their axioms,
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


MODULES = [('KFCausalPartialFourierSlices', 6), ('KFCausalPartialFourierIntegral', 5), ('KFCausalPartialFourierDilation', 7), ('KFCausalClockFloorSpectatorChart', 13), ('KFCausalClockFloorPairedChart', 9), ('KFCausalClockFloorPairedStraightening', 11), ('KFCausalClockFloorMixedProduct', 6), ('KFCausalWeightedTensorRepresentative', 4), ('KFCausalClockFloorMixedChart', 4), ('KFCausalClockFloorMixedCoordinates', 7), ('KFCausalClockFloorMixedRadial', 6), ('KFCausalClockFloorMixedSymbols', 4), ('KFCausalClockFloorMixedHeatStrip', 8), ('KFCausalClockFloorMixedRadialStrip', 9)]


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
    logs = overlay/'physical-clock-floor-mixed-radial-strip-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_position_radial_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_mixed_radial_strip_audit.py']
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
        scope='For continuous joint L1/L2 functions on arbitrary Euclidean product blocks, slice Plancherel and Fubini derive L2 membership of the partial Fourier integral, and dense tensor pairings identify it with the actual partial Fourier unitary. Positive continuous spectator-dependent dilations satisfy the exact Fourier scaling law on continuous L1/L2 left factors and compactly supported continuous right factors; all required integrability is derived. The actual physical clock chart is identified in paired coordinates, including the inverse chart, transverse dilation and neutral shear. Its actual L2 clock-straightening unitary is conjugated by the existing partial Fourier unitary. A proved null-set-preserving mixed map and dense-factor closed-submodule argument extend the weighted representative identity to every L2 state. Writing q for the straightened clock, z=chartInverse(epsilon,q), R=exp(z/2), and sigma=1/sqrt(2), the mixed map sends (xi,(q,s1,s2,r)) to (R^-1*xi,(z,R*s1,R*s2,r+4*sigma*(R-1)*s2)); the weight is (exp(z)+epsilon)^(-1/2). This identity is then applied to the original physical heat and radial test operators on all physical L2 states. Their transformed symbols are exp(-2*delta*exp(-z)*(2*pi*hbar*xi1)^2) and exp(-2*delta*(exp(-z)*(2*pi*hbar*xi1)^2+exp(z)*s2^2))*exp(i*v*(r+4*sigma*(exp(z/2)-1)*s2)), respectively. The complex inverse clock chart gives analytic continuations in q. For positive epsilon and delta and abs(Im(q))<=pi*epsilon/3, the heat multiplier has norm at most one and the radial multiplier has norm at most exp(v^2*Im(q)^2/(2*delta*epsilon^2)), uniformly over all other coordinates. Real-slice identification with the actual transformed physical operators is proved on all L2 vectors. These results close the real partial-Fourier/clock-dilation identification and establish the associated analytic multiplier bounds. They do not yet identify the longitudinal exponential graph in these mixed coordinates: commutation of the transverse partial Fourier change with the actual clock spectral exponential remains to be proved. Consequently full ordered matter-domain preservation for the radial test, its full charge-averaged form action, energy graph-norm cutoff removal, normalized full Hamiltonian response, neutral-position time variation and tightness remain open. The strip bound alone is not uniform as delta tends to zero at fixed nonzero hbar and v. Full twelve-dimensional dynamics, negative-clock-momentum control, classical force closure and uniqueness, clock-defect removal, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain unproved. The Hamiltonian and physical model are unchanged; no necessity of a model change is established. All 1080 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_mixed_radial_strip_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
