#!/usr/bin/env python3
"""Resolve the completed scalar phase's fifth coefficient on a finite chart.

This is a generic 2^4 field, not the two-coordinate continuum refinement.
Odd polynomial fits at two amplitude ranges diagnose coefficient stability;
they are not rigorous derivative bounds or a continuum scaling estimate.
"""
import hashlib
import argparse
import json
from pathlib import Path
import time

import numpy as np
import second_cohomology_audit as completion
from radial_measure_audit import RectangularOverlap, positive_current

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-phase', action='store_true',
                        help='Reuse the recorded phase samples after checking their inputs and dependencies')
    parser.add_argument('--check-quadrature', action='store_true',
                        help='Check two phase samples with higher quadrature and the odd-field relation')
    args = parser.parse_args()
    started = time.time()
    model = RectangularOverlap((2,)*4)
    field = np.random.default_rng(261029019).uniform(-.15, .15, (4, model.n))
    # Charge homogeneity at the Taylor coefficient: sum m q^5 = 4320.
    # Computing a single charge avoids cancellation of the lower moments.
    completion.SPECIES = [('unit charge', 1, 1)]
    rows = []
    output = ROOT/'data/chiral_completed_phase_response.json'
    provenance = None
    if args.reuse_phase:
        previous = json.loads(output.read_text())
        assert previous['field_seed'] == 261029019 and previous['maximum_field'] == .15
        assert previous['lengths'] == [2]*4
        for path, digest in previous['source_sha256'].items():
            if path != 'scripts/chiral_completed_phase_response.py':
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
        rows = previous['rows']
        assert [r['amplitude'] for r in rows] == [.2, .3, .4, .5, .6, .75, .9, 1.]
        provenance = previous.get('reused_phase_provenance',
                                  dict(source_sha256=previous['source_sha256'],
                                       elapsed_seconds=previous['elapsed_seconds']))
    else:
        for amplitude in [.2, .3, .4, .5, .6, .75, .9, 1.]:
            result = completion.integrated_jets(model, amplitude*field,
                                               field_nodes=6, resolvent_nodes=40)
            rows.append(dict(amplitude=amplitude, correction=result['phase'],
                             audit=result['audit']))
            print('phase', amplitude, result['phase'], flush=True)
    for row in rows:
        row['bare_positive_current_imag'] = -positive_current(
            model, np.exp(1j*row['amplitude']*field), 1, field)
    fits = []
    for selection in [rows, rows[:5], rows[2:]]:
        x = np.array([r['amplitude'] for r in selection])
        y = np.array([r['correction'] for r in selection])/x**3
        degree = min(3, len(selection)-1)
        coefficients = np.polynomial.polynomial.polyfit(x*x, y, degree)
        current = np.array([r['bare_positive_current_imag'] for r in selection])
        bare = np.polynomial.polynomial.polyfit(x*x, current, min(4, len(selection)-1))
        predicted = np.polynomial.polynomial.polyval(x*x, coefficients)*x**3
        fits.append(dict(amplitudes=x.tolist(), odd_orders=list(range(3, 4+2*degree, 2)),
                         coefficients=coefficients.tolist(),
                         maximum_fit_residual=float(max(abs(predicted-np.array([r['correction'] for r in selection])))),
                         single_charge_phase_t5=float(coefficients[1]),
                         bare_current_even_coefficients=bare.tolist(),
                         single_charge_bare_current_t4_imag=float(bare[2]),
                         single_charge_completed_current_t4_imag=float(bare[2]+5*coefficients[1]),
                         supplied_generation_current_t4_correction_imag=float(5*4320*coefficients[1])))
    report = dict(schema_version=1, field_seed=261029019, maximum_field=.15,
                  lengths=[2]*4, rows=rows, fits=fits, completed_phase_included=True,
                  continuum_scaling_proved=False,
                  convention='W_plus,completed = W_plus,Kato exp(+i C); delta beta = 5i [t^5] C',
                  scope='Finite-chart polynomial-fit diagnostic; distinct from the two-coordinate continuum field',
                  elapsed_seconds=time.time()-started)
    if provenance is not None:
        report['reused_phase_provenance'] = provenance
        if 'quadrature_controls' in previous and not args.check_quadrature:
            report['quadrature_controls'] = previous['quadrature_controls']
            report['field_reversal_oddness_error'] = previous['field_reversal_oddness_error']
            report['reused_quadrature_controls'] = True
    if args.check_quadrature:
        checks = []
        for amplitude in [.6, 1.]:
            refined = completion.integrated_jets(model, amplitude*field,
                                                 field_nodes=10, resolvent_nodes=64)
            original = next(r['correction'] for r in rows if r['amplitude'] == amplitude)
            error = abs(refined['phase']-original)
            assert error < 1e-12
            checks.append(dict(amplitude=amplitude, field_nodes=10, resolvent_nodes=64,
                               correction=refined['phase'], absolute_change=error))
        reversed_field = completion.integrated_jets(model, -field,
                                                   field_nodes=6, resolvent_nodes=40)
        odd_error = abs(reversed_field['phase']+rows[-1]['correction'])
        assert odd_error < 1e-12
        report['quadrature_controls'] = checks
        report['field_reversal_oddness_error'] = odd_error
    report['elapsed_seconds'] = time.time()-started
    report['timing_scope'] = 'This invocation; reused sampling/controls are excluded when indicated'
    sources = ['scripts/chiral_completed_phase_response.py', 'scripts/second_cohomology_audit.py',
               'scripts/local_cohomology_audit.py', 'scripts/radial_measure_audit.py']
    report['source_sha256'] = {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}
    output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(fits, indent=2), flush=True)


if __name__ == '__main__':
    main()
