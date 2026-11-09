#!/usr/bin/env python3
"""Audit actual neutral spacetime force measures, local limits and window response identification.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_spacetime_force_audit.py --overlay PATH

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


MODULES = [('KFCausalFiniteKernelSpacetime', 8), ('KFCausalSpacetimeForcePair', 6), ('KFCausalNeutralSpacetimeForce', 4), ('KFCausalCompactSpacetimeForce', 4), ('KFCausalLocalSpacetimeTests', 13), ('KFCausalSpacetimeWindowTests', 4), ('KFCausalNeutralSpacetimeLimit', 2)]


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
    logs = overlay/'physical-clock-floor-neutral-spacetime-force-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_consistent_dynamics_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_spacetime_force_audit.py']
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
        scope='For any measurable real-time real-momentum kernel with finite values and continuous total mass, cutting the source time to a compact interval produces a finite kernel with a derived uniform bound. Its composition-product with restricted Lebesgue measure is an actual finite positive spacetime measure on R x R. This construction requires no global uniform kernel bound. Rectangle evaluations and bounded-continuous spacetime test integrals equal the corresponding iterated kernel integrals. The total mass equals the existing integrated momentum measure. Restricting to any smaller time interval and projecting to momentum recovers exactly that interval measure. A bound on the kernel mass controls the time marginal on every measurable time set; for two kernels the bound uses their combined mass with no extra factor of two. Two such measures define a finite spacetime force pair acting by half their difference. Applying the construction to the actual positive and negative output-time kernels yields actual quantum spacetime force measures with the established exact interval slices and total mass. The derived physical energy bound controls their combined mass by interval length times forceBudget, uniformly over positive resolvent scales and all endpoints in a finite symmetric time window. It also bounds their combined time marginal on every measurable time set by forceBudget times restricted Lebesgue measure, eventually uniformly in hbar, scales, endpoints and measurable sets. Nonnegative matter coefficients suffice for these bounds. Both time and momentum are compactified by arctangent into a fixed compact square. Countably many spacetime force-window pairs with separate eventual mass bounds have a common subsequence of positive and negative weak compactified limits. Restriction to the open square and tangent pushforward gives actual finite positive countably additive measures on R x R. Possible compactification boundary mass is retained separately, not assumed absent. Every continuous complex spacetime test vanishing at infinity extends continuously by zero to that square boundary, so all C0 spacetime force actions converge to these local finite measures. The local combined mass inherits each eventual bound. Urysohn time cutoffs are constructed which equal one on a chosen physical time window and zero at compactified time endpoints. Multiplying such a cutoff by the zero extension of a C0 momentum test yields a boundary-vanishing compactified spacetime test. For the actual quantum spacetime pair its evaluation equals the original integrated interval force evaluation exactly. The actual-model existence theorem constructs ONE subsequence carrying the same weakly continuous all-real-time neutral probability curve and initial Dirac law, original characteristic convergence at every time/frequency, fixed-time weak probability convergence, the previously derived consistent interval-force family and Schwartz continuity equation, and positive/negative compactified spacetime limits for ANY chosen countable family of ordered real windows. On that subsequence all C0 spacetime force actions converge, each local spacetime pair has the physical interval-length mass bound, and every admissible time cutoff identifies its whole-window C0 momentum response with the corresponding consistent interval force. In particular every Schwartz probability increment equals the local spacetime force applied to the lifted derivative, with an actual constructed time cutoff. The full theorem retains fixed positive floor and width, strictly positive matter coefficients, an admissible nonzero hbar sequence tending to zero and any positive diverging resolvent scale sequence. These results construct genuine finite countably additive spacetime force measures separately on all chosen windows, linked to the derived whole-window weak balance. They do NOT yet prove convergence of arbitrary time slices, absence of time atoms in the limiting measures, agreement of the local spacetime limits on overlapping windows, a single global spacetime force measure, or the full continuity equation against arbitrary time-dependent spacetime tests. Passing the established prelimit time-marginal domination to the limits and identifying restrictions remain open. Global positive-force tightness and vanishing escaped momentum mass are not assumed or proved. A closed classical force functional, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 976 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_spacetime_force_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
