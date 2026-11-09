#!/usr/bin/env python3
"""Noncommuting energy constraints, quantum prefix clocks, and their limits."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy


I2 = np.eye(2)
X = np.array([[0., 1.], [1., 0.]])
Z = np.diag([1., -1.])


def norm(a):
    return float(la.norm(a, 2))


def comm(a, b):
    return a @ b-b @ a


def kron_all(factors):
    result = np.ones((1, 1))
    for factor in factors:
        result = np.kron(result, factor)
    return result


def exact_identities():
    x, z, identity = sy.Matrix(X.astype(int)), sy.Matrix(Z.astype(int)), sy.eye(2)
    a = sy.kronecker_product(x, x, identity)
    b = sy.kronecker_product(identity, z, z)
    assert a*a == b*b == sy.eye(8)
    assert a*b+b*a == sy.zeros(8)
    theta = sy.Symbol('theta', real=True)
    dressed = b*sy.cos(2*theta)-sy.I*a*b*sy.sin(2*theta)
    assert (sy.I*sy.diff(dressed, theta)-(a*dressed-dressed*a)).applyfunc(sy.simplify) == sy.zeros(8)
    f, g = sy.symbols('f g', real=True)
    assert sy.expand((f*a+g*b)**2-(f*f+g*g)*sy.eye(8)) == sy.zeros(8)
    return dict(anticommuting_positive_energy_projectors=True,
                clock_derivative_cancels_energy_commutator=True,
                exact_record_error_spectrum_identity=True,
                scope="Exact finite Pauli algebra underlying the no-recording bound and the two-clock repair.")


def incompatible_records():
    a, b = kron_all([X, X, I2]), kron_all([I2, Z, Z])
    pa, pb, ident = (np.eye(8)+a)/2, (np.eye(8)+b)/2, np.eye(8)
    rows = []
    for radius, angle in itertools.product([0., .15, .5, .8, 1.3], [0., .3, 1.2, 2.7]):
        f, g = .5+radius*np.cos(angle), .5+radius*np.sin(angle)
        ca, cb = f*ident-pa, g*ident-pb
        smallest = float(min(la.eigvalsh(ca @ ca+cb @ cb)))
        prediction = (radius-.5)**2+.25
        assert abs(smallest-prediction) < 2e-13
        assert smallest >= .25-1e-13
        rows.append(dict(first_flux=f, second_flux=g, minimum_master_constraint=smallest,
                         exact_prediction=prediction, uniform_residual_floor=.25))
    return dict(cases=rows, scope="Joint spectral fibers of commuting ancillary fluxes independent of two positive noncommuting matter energies. The analytical bound applies to arbitrary register dimensions.")


def chain_terms(sites):
    raw = np.kron(X, X)+.4*np.kron(Z, Z)+.23*np.kron(Z, I2)
    local = raw/norm(raw)
    return [kron_all([np.eye(2**j), local, np.eye(2**(sites-j-2))])
            for j in range(sites-1)]


def prefix_connection(terms, angles):
    dimension = terms[0].shape[0]
    prefix, product = np.zeros((dimension, dimension), complex), np.eye(dimension, dtype=complex)
    sources, fluxes = [], []
    for h, theta in zip(terms, angles):
        prefix = prefix+h
        sources.append(product @ h @ product.conj().T)
        fluxes.append(product @ prefix @ product.conj().T)
        product = product @ la.expm(-1j*theta*prefix)
    return product, sources, fluxes


def connection_checks():
    rng, rows, step = np.random.default_rng(9112637), [], 1e-5
    for sites in [4, 5, 6]:
        terms = chain_terms(sites)
        total = sum(terms)
        for case in range(2):
            angles = rng.uniform(-.4, .4, size=len(terms))
            w, source, flux = prefix_connection(terms, angles)
            previous = np.zeros_like(total)
            for h, k, f in zip(terms, source, flux):
                assert norm(f-previous-k) < 2e-12
                assert abs(norm(k)-norm(h)) < 2e-12
                previous = f
            derivatives = {}
            for axis in range(len(terms)):
                plus, minus = angles.copy(), angles.copy()
                plus[axis] += step
                minus[axis] -= step
                wp, sp_, _ = prefix_connection(terms, plus)
                wm, sm, _ = prefix_connection(terms, minus)
                derivatives[axis] = [(p-m)/(2*step) for p, m in zip(sp_, sm)]
                if axis == len(terms)-1:
                    boundary_error = norm(1j*(wp-wm)/(2*step)-w @ total)
                    assert boundary_error < 2e-8
            worst = 0.
            for j in range(len(terms)):
                for k in range(j+1, len(terms)):
                    djk = derivatives[j][k]-(derivatives[j-1][k] if j > 0 else 0)
                    dkj = derivatives[k][j]-derivatives[k-1][j]
                    curvature = -1j*djk+1j*dkj+comm(source[j], source[k])
                    worst = max(worst, norm(curvature))
            assert worst < 3e-8
            # The first infinitesimal dressing is independently the energy current.
            zero = np.zeros(len(terms))
            zero[-2] = step
            _, first, _ = prefix_connection(terms, zero)
            zero[-2] = -step
            _, second, _ = prefix_connection(terms, zero)
            current_error = norm((first[-1]-second[-1])/(2*step)+1j*comm(terms[-2], terms[-1]))
            assert current_error < 2e-8
            rows.append(dict(sites=sites, case=case, angles=angles.tolist(),
                             maximum_finite_difference_flatness_error=worst,
                             boundary_generator_derivative_error=boundary_error,
                             first_clock_energy_current_error=current_error))
    return dict(cases=rows, scope="Full finite spin-chain matrices. Differential flatness follows analytically by common unitary conjugation; finite differences independently check its signs, prefix ordering, boundary action and current correction.")


def local_source(terms, angles, radius):
    target = len(terms)-1
    start = target-radius
    product = np.eye(terms[0].shape[0], dtype=complex)
    prefix = np.zeros_like(product)
    for index in range(start, target):
        prefix = prefix+terms[index]
        product = product @ la.expm(-1j*angles[index]*prefix)
    return product @ terms[target] @ product.conj().T, start


def small_chart_locality():
    rng, rows = np.random.default_rng(9112638), []
    for sites in [5, 6, 7]:
        terms = chain_terms(sites)
        for delta in [.005, .01, .02]:
            angles = rng.uniform(-delta, delta, size=len(terms))
            full = prefix_connection(terms, angles)[1][-1]
            mu, strength = 1., 1.
            alpha = 8*strength*np.exp(mu)
            beta = mu-alpha*delta
            assert beta > 0
            for radius in [1, 2, 3]:
                approximate, left_sites = local_source(terms, angles, radius)
                error = norm(full-approximate)
                bound = (4*strength*norm(terms[-1])*delta*np.exp(-beta*radius)*
                         (1/((1-np.exp(-mu))*(1-np.exp(-beta)))+radius*np.exp(mu)))
                assert error <= min(2*norm(terms[-1]), bound)+2e-12
                # Verify actual strict support of the constructed local approximation.
                outside, inside = 2**left_sites, 2**(sites-left_sites)
                partial = np.trace(approximate.reshape(outside, inside, outside, inside),
                                   axis1=0, axis2=2)/outside
                support_error = norm(approximate-np.kron(np.eye(outside), partial))
                assert support_error < 3e-12
                rows.append(dict(sites=sites, clock_difference_bound=delta,
                                 retained_clocks=radius, exponential_rate=beta,
                                 actual_source_truncation_error=error,
                                 analytical_truncation_bound=bound,
                                 strict_support_error=support_error))
    return dict(cases=rows, scope="Nearest-neighbor spin chains on a restricted clock chart. The all-size estimate is analytical. These tests do not prove locality of the full finite-clock parent or a three-dimensional gravitational phase.")


def finite_clock_checks():
    a, b = kron_all([X, X, I2]), kron_all([I2, Z, Z])
    total, rows = a+b, []
    for dimension in [3, 5, 7]:
        mmax = dimension//2
        angles = 2*np.pi*np.arange(dimension)/dimension
        frequencies = np.arange(-mmax, mmax+1)
        fourier = np.exp(-1j*angles[:, None]*frequencies)/np.sqrt(dimension)
        energy = (fourier*frequencies) @ fourier.conj().T
        w = la.block_diag(*[
            la.expm(-1j*t*a) @ la.expm(-1j*s*total/np.sqrt(2))
            for t in angles for s in angles])
        e1 = kron_all([energy, np.eye(dimension), np.eye(8)])
        e2 = np.sqrt(2)*kron_all([np.eye(dimension), energy, np.eye(8)])
        c1, c2 = w @ e1 @ w.conj().T, w @ (e2-e1) @ w.conj().T
        reference = np.kron(np.ones((dimension**2, 1))/dimension, np.eye(8))
        v = w @ reference
        assert norm(v.conj().T @ v-np.eye(8)) < 1e-12
        closure = norm(comm(c1, c2))
        boundary = norm(e2 @ v-v @ total)
        assert closure < 2e-11
        assert boundary < 2e-12
        assert norm(c1 @ v)+norm(c2 @ v) < 3e-12
        master = c1 @ c1+c2 @ c2
        spectrum = la.eigvalsh(master)
        assert np.sum(abs(spectrum) < 1e-10) == 8
        assert spectrum[8] >= 1-2e-11
        parent = 10*master+e2+np.sqrt(2)*np.eye(e1.shape[0])
        parent_spectrum = la.eigvalsh(parent)
        expected = np.array([0.]*4+[2*np.sqrt(2)]*4)
        assert max(abs(parent_spectrum[:8]-expected)) < 2e-9
        exclusion_bound = 10-(mmax-1)*np.sqrt(2)
        assert parent_spectrum[8] >= exclusion_bound-1e-10 > 2*np.sqrt(2)
        assert norm(parent @ v-v @ (total+np.sqrt(2)*np.eye(8))) < 2e-11
        for time in [.13, .7]:
            assert norm(la.expm(-1j*time*e2) @ v-v @ la.expm(-1j*time*total)) < 3e-12
        # Physical observables are dressed, and preserve the complete code algebra.
        matter_o = kron_all([Z, I2, I2])
        physical_o = w @ np.kron(np.eye(dimension**2), matter_o) @ w.conj().T
        assert norm(comm(c1, physical_o))+norm(comm(c2, physical_o)) < 3e-11
        assert norm(comm(e2, physical_o) @ v-v @ comm(total, matter_o)) < 3e-12
        f1 = e1-np.kron(np.eye(dimension**2), a)
        dressed_b = la.block_diag(*[
            la.expm(-1j*t*a) @ b @ la.expm(1j*t*a)
            for t in angles for _ in angles])
        f2 = e2-e1-dressed_b
        inner = fourier[:, abs(frequencies) <= mmax-1]
        inner_band = kron_all([inner, inner, np.eye(8)])
        form_error = norm((c1-f1) @ inner_band)+norm((c2-f2) @ inner_band)
        assert form_error < 2e-11
        assert norm(f1 @ v)+norm(f2 @ v) < 4e-12
        full_form_error = norm(c1-f1)+norm(c2-f2)
        naive_closure = norm(comm(f1, f2))
        assert full_form_error > dimension
        assert naive_closure > 1
        rows.append(dict(clock_dimension=dimension, full_dimension=e1.shape[0],
                         physical_dimension=8, exact_constraint_commutator_error=closure,
                         boundary_energy_intertwining_error=boundary,
                         smallest_excluded_master_eigenvalue=float(spectrum[8]),
                         smallest_excluded_parent_energy=float(parent_spectrum[8]),
                         proved_excluded_parent_lower_bound=float(exclusion_bound),
                         restricted_form_error=form_error,
                         full_clock_form_error=full_form_error,
                         full_naive_constraint_commutator=naive_closure))
    return dict(cases=rows, scope="Exact finite registers for two individually commensurate prefix spectra. Full code, parent spectra and encoded dynamics are checked. The clock cutoff repairs are essential; this is a finite patch, not a uniform local thermodynamic realization.")


def clock_action(state, axis, spacing, time=None):
    """Apply one clock energy or its time evolution, with exp(-i m theta) modes."""
    dimension = state.shape[axis]
    energies = spacing*np.rint(np.fft.fftfreq(dimension)*dimension)
    multiplier = energies if time is None else np.exp(-1j*time*energies)
    shape = [1]*state.ndim
    shape[axis] = dimension
    return np.fft.fft(np.fft.ifft(state, axis=axis)*multiplier.reshape(shape), axis=axis)


def rounded_prefix_checks():
    rows = []
    for sites, spacing in itertools.product([3, 4], [.25, .5]):
        terms = chain_terms(sites)
        clocks, matter = len(terms), terms[0].shape[0]
        prefixes, rounded, spectral = [], [], []
        prefix = np.zeros((matter, matter))
        maximum_frequency, rounding_error = 0, 0.
        for term in terms:
            prefix = prefix+term
            eigenvalues, eigenvectors = la.eigh(prefix)
            integers = np.rint(eigenvalues/spacing).astype(int)
            replacement = (eigenvectors*(spacing*integers)) @ eigenvectors.conj().T
            error = norm(replacement-prefix)
            assert error <= spacing/2+2e-13
            maximum_frequency = max(maximum_frequency, int(max(abs(integers))))
            rounding_error = max(rounding_error, error)
            prefixes.append(prefix.copy())
            rounded.append(replacement)
            spectral.append((integers, eigenvectors))
        mmax = max(1, maximum_frequency)
        dimension = 2*mmax+1
        angles = 2*np.pi*np.arange(dimension)/(dimension*spacing)
        factors = [np.array([(vectors*np.exp(-1j*theta*spacing*integers)) @ vectors.conj().T
                             for theta in angles])
                   for integers, vectors in spectral]
        # Store the entire physical encoding, but never a squared full-space operator.
        w = factors[0]
        for factor in factors[1:]:
            w = w[..., None, :, :] @ factor
        assert w.shape == (dimension,)*clocks+(matter, matter)
        v = w/dimension**(clocks/2)
        vflat = v.reshape(-1, matter)
        isometry_error = norm(vflat.conj().T @ vflat-np.eye(matter))
        assert isometry_error < 2e-12
        boundary_error = norm((clock_action(v, clocks-1, spacing)-v @ rounded[-1]).reshape(-1, matter))
        assert boundary_error < 2e-11
        reference = np.swapaxes(w.conj(), -1, -2) @ v
        residuals, previous = [], np.zeros_like(v)
        for axis in range(clocks):
            current = clock_action(reference, axis, spacing)
            residuals.append(norm((w @ (current-previous)).reshape(-1, matter)))
            previous = current
        assert max(residuals) < 2e-11
        evolution = []
        for time in [.13, .7, 1.4]:
            actual = clock_action(v, clocks-1, spacing, time=time)
            exact_error = norm((actual-v @ la.expm(-1j*time*rounded[-1])).reshape(-1, matter))
            approximate_error = norm((actual-v @ la.expm(-1j*time*prefixes[-1])).reshape(-1, matter))
            assert exact_error < 2e-11
            assert approximate_error <= abs(time)*spacing/2+2e-11
            evolution.append(dict(time=time, rounded_evolution_error=exact_error,
                                  supplied_evolution_error=approximate_error,
                                  supplied_evolution_error_bound=abs(time)*spacing/2))
        small_angles = np.linspace(-.02, .017, clocks)
        differences = [rounded[0]]+[rounded[j]-rounded[j-1] for j in range(1, clocks)]
        sources = prefix_connection(terms, small_angles)[1]
        rounded_sources = prefix_connection(differences, small_angles)[1]
        source_errors, source_bounds = [], []
        for j in range(clocks):
            error = norm(rounded_sources[j]-sources[j])
            bound = spacing*(1+sum(abs(small_angles[:j])))
            assert error <= bound+2e-12
            source_errors.append(error)
            source_bounds.append(float(bound))
        # The encoded history has uniform clock-coordinate probabilities for
        # every matter state. A local coordinate chart need not contain its norm.
        delta = .02
        centered_angles = angles.copy()
        centered_angles[centered_angles > np.pi/spacing] -= 2*np.pi/spacing
        chart_indices = np.flatnonzero(abs(centered_angles) <= delta)
        restricted = v
        for axis in range(clocks-1):
            restricted = np.take(restricted, chart_indices, axis=axis)
        restricted = restricted.reshape(-1, matter)
        chart_probability = (len(chart_indices)/dimension)**(clocks-1)
        chart_probability_error = norm(restricted.conj().T @ restricted-chart_probability*np.eye(matter))
        assert chart_probability_error < 2e-12
        assert len(chart_indices)/dimension <= delta*spacing/np.pi+1/dimension+1e-14
        # The conjugated master's spectrum is the reference spectrum exactly.
        # Enumerate only the clock labels; the matter multiplicity is unchanged.
        labels = np.array(list(itertools.product(range(-mmax, mmax+1), repeat=clocks)))
        squared_steps = np.sum(np.diff(labels, axis=1, prepend=0)**2, axis=1)
        assert np.count_nonzero(squared_steps == 0) == 1
        assert min(squared_steps[squared_steps > 0]) == 1
        penalty = (2*mmax*spacing+1)/spacing**2
        rmin, rmax = float(min(la.eigvalsh(rounded[-1]))), float(max(la.eigvalsh(rounded[-1])))
        excluded_bound = penalty*spacing**2-mmax*spacing-rmin
        physical_top = rmax-rmin
        assert excluded_bound >= physical_top+1-2e-12
        rows.append(dict(sites=sites, clocks=clocks, energy_spacing=spacing,
                         clock_dimension=dimension, full_dimension=dimension**clocks*matter,
                         physical_dimension=matter, maximum_prefix_rounding_error=rounding_error,
                         isometry_error=isometry_error, boundary_energy_intertwining_error=boundary_error,
                         maximum_constraint_on_code_error=max(residuals), time_evolution=evolution,
                         chart_source_errors=source_errors, chart_source_error_bounds=source_bounds,
                         chart_half_width=delta, probability_in_small_clock_chart=chart_probability,
                         chart_probability_identity_error=chart_probability_error,
                         reference_master_gap=spacing**2, penalty_coefficient=penalty,
                         proved_excluded_parent_lower_bound=excluded_bound,
                         physical_band_upper_edge=physical_top))
    return dict(cases=rows, scope="Full encoding maps for generic finite prefix spectra after spectral rounding. Boundary evolution and constraint kernel are checked without materializing full-space matrices. The gap follows by common conjugation and is independently checked on every clock Fourier label. Register dimension, penalty and nonlocal spectral computation are resources; this is not a fixed-spin local phase.")


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_identities(), incompatible_energy_records=incompatible_records(),
                  continuous_connection=connection_checks(), chart_locality=small_chart_locality(),
                  finite_quantum_clocks=finite_clock_checks(),
                  rounded_prefix_clocks=rounded_prefix_checks())
    sources = ['QUANTUM_ENERGY_DRESSING.md', 'scripts/quantum_energy_dressing_audit.py',
               'GRAVITATIONAL_BOUNDARY_DRESSING.md', 'CAUSAL_VACUUM_SELECTION.md',
               'SPIN_CLOCK_BRACKET.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'CAUSAL_ORDER_CLOCK_BRIDGE.md', 'LOCAL_CAUSAL_CLOCK.md',
               'PREPOTENTIAL_LATTICE_BRIDGE.md', 'COMPACT_CONSTRAINT_NORMALIZER.md',
               'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = (
        'Commuting ancillary energy records fail for incompatible positive local terms. '
        'A quantum prefix-clock connection repairs the noncommuting source problem and '
        'represents the supplied total Hamiltonian at its final clock. A small-chart '
        'nearest-neighbor locality estimate, an exact finite-register realization, and '
        'spectrally rounded finite encodings of general prefix Hamiltonians are checked. '
        'The rounded dynamics approximate supplied dynamics with an explicit error; '
        'the encoding does not select that Hamiltonian. '
        'No uniformly local finite-spin gravitational phase, Einstein deformation algebra, '
        'universal coupling, Standard Model dynamics, or TOE is proved. No Lean theorem.')
    target = root/'data/quantum_energy_dressing_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         exact_algebra=True, source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
