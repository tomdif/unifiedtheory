#!/usr/bin/env python3
"""Controlled large-spin / fast-geometry collective-wave checks.

This audits a specified extension. It does not establish its ordered phase
at spin 1/2, a physical causal order, or Einstein gravity.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy
from scipy import sparse as sp
from scipy.sparse.linalg import LinearOperator, cg, eigsh

from collective_spacetime_audit import QuantumFiber


def spin_expansion():
    X = np.array([[0., 1.], [1., 0.]])
    Y = np.array([[0., -1j], [1j, 0.]])
    lower = np.array([[0., 1.], [0., 0.]])
    kappa = .25
    spin_half = -2*kappa*(np.kron(X/2, X/2)+np.kron(Y/2, Y/2))
    hopping = -kappa*(np.kron(lower.T, lower)+np.kron(lower, lower.T))
    assert np.array_equal(spin_half, hopping)
    q2, p2, cross, N, k = sy.symbols('q2 p2 cross N k', real=True)
    identity = k*(6*(q2+p2-N)/2-cross)-(3*k*p2+k*(6*q2-2*cross)/2-3*k*N)
    assert sy.expand(identity) == 0
    rows = []
    for m in [1, 2, 3]:
        D = m+3  # Preserve all outputs from the input occupation cutoff.
        a = np.diag(np.sqrt(np.arange(1, D)), 1)
        number, I = np.diag(np.arange(D)), np.eye(D)
        q, pi = (a+a.T)/np.sqrt(2), (a-a.T)/(1j*np.sqrt(2))
        assert la.norm(((q@q+pi@pi-I)/2-number)[:, :m+1]) < 1e-12
        source = [i*D+j for i in range(m+1) for j in range(m+1)]
        quadratic = kappa*(np.kron(number, I)+np.kron(I, number)-np.kron(q, q))
        for S in [2., 4., 8., 16., 32., 64.]:
            assert 2*S >= m+1
            root = np.diag(np.sqrt(np.maximum(2*S-np.arange(D), 0.)))
            sx, sy_spin = S*I-number, (root@a+a.T@root)/2
            yS = sy_spin/np.sqrt(S)
            one_error = float(la.norm((yS-q)[:, :m+1], 2))
            one_bound = m*np.sqrt(m+1)/(np.sqrt(2)*S)
            assert one_error <= one_bound+1e-12
            bond = -kappa/S*(np.kron(sx, sx)+np.kron(sy_spin, sy_spin))+kappa*S*np.eye(D*D)
            error = float(la.norm((bond-quadratic)[:, source], 2))
            bound = kappa*(3*m*m+2*m)/S
            assert error <= bound+1e-11
            rows.append(dict(S=S, maximum_input_occupation=m, local_quadrature_error=one_error,
                             local_quadrature_bound=one_bound, bond_error=error, bond_bound=bound,
                             error_times_S=error*S))
    return dict(spin_half_hopping_identity=True, degree_six_algebraic_identity=True,
                low_occupation_operator_checks=rows,
                scope='Finite-column Holstein-Primakoff operator checks with output margins, not a finite-S ordered-phase proof.')


def fast_geometry_oscillator():
    D, kappa, b, d = 24, .25, .4, .31
    omega = np.sqrt(d*d+4*b*b)
    p = (1-d/omega)/2
    g = np.array([np.sqrt(1-p), np.sqrt(p)])
    geometry = np.array([[(omega-d)/2, -b], [-b, (omega+d)/2]])
    assert la.norm(geometry@g) < 1e-14
    a = np.diag(np.sqrt(np.arange(1, D)), 1)
    q, pi = (a+a.T)/np.sqrt(2), (a-a.T)/(1j*np.sqrt(2))
    kinetic = 3*kappa*(pi@pi)
    potential = kappa/2*(q@q)
    stiffness = np.diag([1., 4.])
    mean = kinetic+(1+3*p)*potential
    field0 = np.eye(D)[:, 0]
    initial = np.kron(g, field0)
    embedding = np.kron(g[:, None], np.eye(D))
    projector = embedding@embedding.conj().T
    energy = float(np.vdot(field0, mean@field0).real)
    rows = []
    for scale in [1., 4., 16., 64., 256.]:
        H = scale*np.kron(geometry, np.eye(D))+np.kron(np.eye(2), kinetic)+np.kron(stiffness, potential)
        assert la.eigvalsh(H)[0] >= -1e-12
        errors, leakages, tails = [], [], []
        for time in [.2, .7, 1.3]:
            actual = la.expm(-1j*time*H)@initial
            target = embedding@(la.expm(-1j*time*mean)@field0)
            error = float(la.norm(actual-target))
            leakage = float(la.norm(actual-projector@actual)**2)
            assert leakage <= energy/(scale*omega)+1e-12
            errors.append(error)
            leakages.append(leakage)
            tails.append(float(np.sum(np.abs(actual.reshape(2, D)[:, -4:])**2)))
        rows.append(dict(geometry_scale=scale, maximum_state_error=max(errors),
                         maximum_geometry_leakage=max(leakages), uniform_energy_leakage_bound=energy/(scale*omega),
                         largest_high_occupation_probability=max(tails)))
    assert rows[-1]['maximum_state_error'] < rows[0]['maximum_state_error']/20
    return dict(oscillator_cutoff=D, joint_dimension=2*D, initial_energy=energy, rows=rows,
                scope='A truncated one-oscillator / two-level-geometry benchmark of the fast-gap mechanism; the infinite-field convergence is the separate quadratic-form proof.')


def reduced_inverse(H, ground, source):
    regular = LinearOperator(H.shape, matvec=lambda v: H@v+ground*np.vdot(ground, v), dtype=complex)
    diagonal = H.diagonal().real+np.abs(ground)**2
    preconditioner = LinearOperator(H.shape, matvec=lambda v: v/diagonal, dtype=complex)
    solved, info = cg(regular, source, M=preconditioner, rtol=1e-12, atol=1e-14, maxiter=10000)
    residual = float(la.norm(regular@solved-source))
    assert info == 0 and residual < 1e-10
    return solved, residual


class MeanCell:
    def __init__(self):
        self.quantum = QuantumFiber()
        self.n, self.p, self.kappa = self.quantum.n, self.quantum.p, self.quantum.kappa
        self.g = np.ones(self.n)/np.sqrt(self.n)
        self.H0 = self.hamiltonian([0., 0., 0.]).real.tocsr()
        first, second = self.quantum.derivatives()
        self.first, self.second = self.average_blocks(first), self.average_blocks(second)
        self.source = self.first@self.g
        assert abs(np.vdot(self.source, self.source).real-20*self.kappa**2*self.p**2/self.n) < 1e-13
        solved, self.residual = reduced_inverse(self.H0, self.g, self.source)
        self.diamagnetic = float(np.vdot(self.g, self.second@self.g).real/2)
        self.corrector = float(np.vdot(self.source, solved).real)
        self.D = np.array([self.diamagnetic-self.corrector, self.kappa, self.kappa])
        self.delta = self.kappa*np.sin(np.pi/self.quantum.ell)**2
        self.radius = .5*np.log1p(self.delta/(24*self.kappa))
        self.quartic = self.delta/self.radius**4
        self.cache = {}

    def average_blocks(self, H):
        n = self.n
        return ((1-self.p)*H[:n, :n]+self.p*H[n:, n:]).tocsr()

    def hamiltonian(self, momentum):
        # Project the hopping onto the coherent geometry ground vector.
        # Geometry terms cancel only after retaining their off-diagonal part;
        # subtracting that full operator first is equivalent and explicit.
        return self.average_blocks(self.quantum.hamiltonian(momentum)-self.quantum.geometry)

    def energy(self, momentum):
        key = tuple(float(x) for x in momentum)
        if key not in self.cache:
            if max(map(abs, key)) == 0:
                self.cache[key] = 0.
            else:
                H = self.hamiltonian(key)
                assert sp.linalg.norm(H-H.conj().T) < 1e-12
                energy = float(eigsh(H, k=1, which='SA', tol=1e-12,
                                     v0=self.g.astype(complex), return_eigenvectors=False)[0])
                assert energy >= 0
                self.cache[key] = energy
        return self.cache[key]

    def audit(self):
        assert all(self.kappa/4 <= x <= 4*self.kappa for x in self.D)
        assert la.norm(self.H0@self.g) < 1e-12
        spectrum = np.sort(eigsh(self.H0, k=2, which='SA', tol=1e-11, return_eigenvectors=False))
        assert abs(spectrum[0]) < 1e-12 and spectrum[1] >= self.delta-1e-11
        bands = []
        for q in [.04, .02, .01, .005, .0005]:
            energy = self.energy([q, 0., 0.])
            frequency = np.sqrt(6*self.kappa*energy)
            if q <= self.radius/2:
                assert abs(energy-self.D[0]*q*q) <= self.quartic*q**4+1e-12
            bands.append(dict(momentum=q, band_energy=energy, collective_frequency=frequency,
                              frequency_over_momentum=frequency/q,
                              limiting_speed=float(np.sqrt(6*self.kappa*self.D[0])),
                              inside_conservative_radius=bool(q <= self.radius/2)))
        errors = [abs(row['frequency_over_momentum']-row['limiting_speed']) for row in bands[:4]]
        assert errors[-1] < errors[0]/30
        transverse_k = np.array([0., .03, -.02])
        transverse_energy = 2*self.kappa*(2-np.cos(.03)-np.cos(.02))
        transverse_residual = float(la.norm(self.hamiltonian(transverse_k)@self.g-transverse_energy*self.g))
        assert transverse_residual < 1e-12
        frequencies = []
        momenta = [np.array(v) for v in [(0., 0., 0.), (1., 0., 0.), (1., .4, -.3)]]
        for a in [.02, .01, .005]:
            for p in momenta:
                exact = np.sqrt(6*self.kappa*self.energy(a*p))/a
                continuum = np.sqrt(6*self.kappa*np.dot(self.D, p*p))
                time = 1.7
                displacement_error = abs(np.cos(time*exact)-np.cos(time*continuum))
                velocity_error = abs(time*np.sinc(time*exact/np.pi)-time*np.sinc(time*continuum/np.pi))
                frequency_error = abs(exact-continuum)
                assert displacement_error <= time*frequency_error+1e-12
                assert velocity_error <= time*time*frequency_error/2+1e-12
                if a*np.sum(abs(p)) <= self.radius/2:
                    bound = 6*np.sqrt(2)*self.quartic*a*a*np.sum(abs(p))**3
                    assert frequency_error <= bound+1e-11
                frequencies.append(dict(spacing=a, continuum_momentum=p.tolist(),
                                        frequency_error=float(frequency_error),
                                        displacement_factor_error=float(displacement_error),
                                        velocity_factor_error=float(velocity_error)))
        C = 6*self.kappa*self.D
        metric = np.diag(np.r_[-1., 1/C])
        inverse_metric = np.diag(np.r_[-1., C])
        assert np.max(abs(metric@inverse_metric-np.eye(4))) < 1e-14
        assert np.sum(la.eigvalsh(metric) < 0) == 1
        for p in momenta:
            covector = np.r_[np.sqrt(np.dot(C, p*p)), p]
            assert abs(covector@inverse_metric@covector) < 1e-13
        return dict(cell_vertices=self.n, active_probability=self.p, spatial_tensor=self.D.tolist(),
                    susceptibility=1/(6*self.kappa), characteristic_speed=np.sqrt(C).tolist(),
                    acoustic_metric_diagonal=np.diag(metric).tolist(),
                    diamagnetic_coefficient=self.diamagnetic, corrector=self.corrector,
                    reduced_inverse_residual=self.residual, fiber_gap_lower_bound=self.delta,
                    analytic_radius=self.radius, quartic_bound_constant=self.quartic,
                    band_rows=bands, wave_evolution_factors=frequencies,
                    transverse_eigenvector_residual=transverse_residual)


def quantum_fast_coefficient(mean):
    rows = []
    for scale in [1., 4., 16., 64., 256.]:
        f = QuantumFiber(rho=.1*scale, J=.005*scale)
        first, second = f.derivatives()
        source = first@f.g
        solved, residual = reduced_inverse(f.H0, f.g, source)
        D = float(np.vdot(f.g, second@f.g).real/2-np.vdot(source, solved).real)
        assert D <= mean.D[0]+1e-12
        rows.append(dict(geometry_scale=scale, quantum_fiber_dimension=f.dim,
                         quantum_Dx=D, limiting_mean_Dx=float(mean.D[0]),
                         coefficient_difference=float(mean.D[0]-D), reduced_inverse_residual=residual))
    assert all(rows[i+1]['quantum_Dx'] >= rows[i]['quantum_Dx']-1e-12 for i in range(len(rows)-1))
    assert rows[-1]['coefficient_difference'] < 2e-6
    return rows


def main():
    root = Path(__file__).resolve().parents[1]
    mean = MeanCell()
    report = dict(spin_expansion=spin_expansion(), fast_geometry_oscillator=fast_geometry_oscillator(),
                  collective_wave=mean.audit(), quantum_fast_coefficient=quantum_fast_coefficient(mean))
    names = ['COLLECTIVE_WAVE_SPACETIME.md', 'scripts/collective_wave_audit.py',
             'UnifiedTheory/Audit/KFCausalCollectiveWave.lean', 'COLLECTIVE_SPACETIME_TEST.md',
             'scripts/collective_spacetime_audit.py', 'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md',
             'LOCAL_CAUSAL_CLOCK.md', 'scripts/local_causal_clock_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('A collective acoustic wave cone in sequential large-spin, fast-geometry, and '
                       'long-wavelength limits about a supplied orientation. No proof of the ordered '
                       'phase at spin 1/2, physical causal-order matching, universal matter cones, '
                       'metric dynamics, or Einstein gravity.')
    (root/'data/collective_wave_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
