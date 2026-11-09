#!/usr/bin/env python3
"""Independent quadrature checks of the damped trial's contour/Fourier signs.

Lean proves strip bounds, contour shifts, exponential Fourier integrability
with a strict width margin, and scalar modulation totality. Finite-window
quadrature does not prove any infinite-domain or density statement.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate
from numpy.polynomial.legendre import leggauss

NEW_MODULES = [
    'KFCausalDampedGaussianStrip', 'KFCausalGaussianContourShift',
    'KFCausalFourierStripDecay', 'KFCausalExponentialFourierDomain',
    'KFCausalDampedGaussianMomentum', 'KFCausalDampedGaussianTotality',
]


def trial(epsilon, a, z):
    return np.exp(-a*z*z/2-epsilon*np.exp(-z/epsilon))


def fourier_line(epsilon, a, y, frequencies):
    result, error = integrate.quad_vec(
        lambda x: np.exp(-2j*np.pi*x*frequencies)*trial(epsilon, a, x+1j*y),
        -12., 12., epsabs=2e-13, epsrel=2e-13, limit=1000)
    return result, float(error)


def main():
    shifts, energies, tails = [], [], []
    frequencies = np.array([-.7, -.25, 0., .3, .65])
    nodes, weights = leggauss(80)
    for epsilon in [.2, .5, 1.]:
        for a in [.8, 2*np.pi]:
            width = np.pi*epsilon/2
            constant = np.exp((a/2)*width**2)*np.sqrt(2*np.pi/a)
            direct, direct_error = fourier_line(epsilon, a, 0., frequencies)
            for ratio in [-.9, -.4, 0., .4, .9]:
                y = ratio*width
                shifted, shifted_error = fourier_line(epsilon, a, y, frequencies)
                reconstructed = np.exp(2*np.pi*frequencies*y)*shifted
                norm_errors = []
                bound_excess = []
                for x in [-6., -2., 0., 1., 4.]:
                    norm = float(abs(trial(epsilon, a, x+1j*y)))
                    formula = np.exp(-a*(x*x-y*y)/2-
                        epsilon*np.exp(-x/epsilon)*np.cos(y/epsilon))
                    norm_errors.append(abs(norm-formula)/max(1., norm, formula))
                    bound_excess.append(norm-np.exp((a/2)*width**2-(a/2)*x*x))
                row = dict(epsilon=epsilon, a=a, imaginary_shift=float(y),
                    frequencies=frequencies.tolist(),
                    shift_identity_error=float(np.max(np.abs(reconstructed-direct))),
                    norm_formula_error=float(max(norm_errors)),
                    sampled_strip_bound_excess=float(max(bound_excess)),
                    direct_quadrature_error_estimate=direct_error,
                    shifted_quadrature_error_estimate=shifted_error)
                assert row['shift_identity_error'] < 2e-9, row
                assert row['norm_formula_error'] < 2e-12, row
                assert row['sampled_strip_bound_excess'] <= 2e-12, row
                shifts.append(row)

            for hbar_ratio in [0., .4, .8]:
                hbar = hbar_ratio*np.pi*epsilon
                values = []
                for cutoff in [4., 8.]:
                    positive_k = (nodes+1)*cutoff/2
                    quadrature_weights = weights*cutoff/2
                    # Opposite contour directions avoid amplification of roundoff
                    # in the exponentially weighted positive/negative tails.
                    total = 0.
                    for sign in [-1., 1.]:
                        ks = sign*positive_k
                        y = -sign*.9*width
                        transformed, _ = fourier_line(epsilon, a, y, ks)
                        density = np.exp((2*np.pi*hbar+4*np.pi*y)*ks)*np.abs(transformed)**2
                        total += float(quadrature_weights@density)
                    values.append(total)
                c = 2*np.pi*(np.pi*epsilon-abs(hbar))
                dominating_integral = constant**2*2/c
                assert 0 < values[0] <= values[1]+2e-9, (epsilon, a, hbar, values)
                assert values[1] < dominating_integral, (epsilon, a, hbar, values)
                real_mass, _ = integrate.quad(lambda x: abs(trial(epsilon, a, x))**2,
                    -12., 12., epsabs=2e-12, epsrel=2e-12)
                row = dict(epsilon=epsilon, a=a, hbar=float(hbar),
                    width_margin=float(np.pi*epsilon-abs(hbar)), frequency_cutoffs=[4., 8.],
                    weighted_fourier_integrals=values, dominating_integral=float(dominating_integral),
                    real_square_integral_in_window=float(real_mass))
                if hbar_ratio == 0.:
                    row['finite_window_plancherel_error'] = abs(values[-1]-real_mass)
                    assert row['finite_window_plancherel_error'] < 2e-8, row
                energies.append(row)

            for ratio in [.98, 1.02]:
                y = ratio*width
                for x in [-2., -4., -8.]:
                    lognorm = -a*(x*x-y*y)/2-epsilon*np.exp(-x/epsilon)*np.cos(y/epsilon)
                    tails.append(dict(epsilon=epsilon, a=a, width_ratio=ratio,
                        real_coordinate=x, log_norm=float(lognorm)))

    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/coupled_longitudinal_domain_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/damped_gaussian_momentum_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    report = dict(contour_cases=shifts, momentum_cases=energies, strip_tail_diagnostics=tails,
        source_sha256=hashes, numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('The concrete repaired scalar trial has proved Gaussian strip bounds, '
            'a derived contour-shift identity, exponential Fourier decay and weighted '
            'Fourier square integrability for abs(hbar)<pi*epsilon. Its momentum '
            'modulations retain this integrability and have dense span in scalar '
            'clock L2. The same modulated family retains the earlier transverse '
            'derivative-energy condition after pullback. Full coupled L2 operator identification, all '
            'matter and charge-averaged energy terms, a dense full six-mode domain, '
            'capacity/regulator limits, physical identification and the TOE remain '
            'open. The strict parameter condition is sufficient for this proof; '
            'failure or necessity outside it is not claimed.'))
    target = root/'data/damped_gaussian_momentum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(shifts), 'contour cases,', len(energies), 'momentum cases,',
        len(hashes), 'source hashes.')
    print('Maximum contour shift error:', max(row['shift_identity_error'] for row in shifts))
    print('Maximum complex norm formula error:', max(row['norm_formula_error'] for row in shifts))
    print('Maximum finite-window Plancherel discrepancy:',
        max(row.get('finite_window_plancherel_error', 0.) for row in energies))


if __name__ == '__main__':
    main()
