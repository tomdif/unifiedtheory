#!/usr/bin/env python3
"""Actual low-band continuum of the regulated quantum switch/probe model.

The analytic infinite-volume and spectral proofs remain in the companion
note. The recovered continuum is Schroedinger, not a derivation of spacetime.
"""
import hashlib
import itertools as it
import json
from pathlib import Path

import numpy as np
import sympy as sy
from scipy import sparse as sp
from scipy.sparse.linalg import LinearOperator, cg, eigsh

from autonomous_geometry_audit import flip_in_place
from patch_geometry_audit import rectangular_torus
from energetic_probe_audit import adjacency_matrix


def exact_forms():
    x, y, z = sy.symbols('x y z', real=True)
    old, new = x*x+y*y+z*z, (x+y)**2+y*y+(y+z)**2
    identity = 3*(4*old-new)-((3*x-y)**2+(3*z-y)**2+y*y)
    assert sy.expand(identity) == 0
    reverse = new.subs({x: x+y, y: -y, z: y+z}, simultaneous=True)
    assert sy.expand(reverse-old) == 0
    M = sy.Matrix([[1, 1, 0], [1, 3, 1], [0, 1, 1]])
    assert set(M.eigenvals()) == {sy.Integer(1), 2-sy.sqrt(3), 2+sy.sqrt(3)}
    return dict(sharp_local_form_constants=['2-sqrt(3)', '2+sqrt(3)'],
                used_global_form_constants=['1/4', '4'],
                exact_sum_of_squares=str(sy.expand(identity)))


class QuantumFiber:
    """Cell-translation-invariant joint fiber in the frame of the probe cell.

    Only the x direction has multiple cells in the finite benchmarks.
    Crossing a cell boundary translates the entire relative bit register.
    """
    def __init__(self, ell=12, cells=1, rho=.1, J=.005, kappa=.25):
        self.ell, self.cells, self.rho, self.J, self.kappa = ell, cells, rho, J, kappa
        self.coords = list(it.product(range(ell), repeat=3))
        self.lookup = {v: i for i, v in enumerate(self.coords)}
        self.n, self.masks = ell**3, 2**cells
        self.dim = self.n*self.masks
        self.b, self.d = 4*rho, 62*J
        self.omega = float(np.sqrt(self.d**2+4*self.b**2))
        self.e0 = self.b+self.d/2-self.omega/2
        self.p = (1-self.d/self.omega)/2
        phi = np.array([(np.sqrt(self.p)**bin(mask).count('1'))
                        *(np.sqrt(1-self.p)**(cells-bin(mask).count('1')))
                        for mask in range(self.masks)])
        self.g = np.repeat(phi/np.sqrt(self.n), self.n)
        bitH = np.zeros((self.masks, self.masks))
        for mask in range(self.masks):
            bitH[mask, mask] = cells*(self.b-self.e0)+self.d*bin(mask).count('1')
            for bit in range(cells):
                bitH[mask ^ (1 << bit), mask] = -self.b
        self.bitH = bitH
        self.geometry = sp.kron(sp.csr_matrix(bitH), sp.eye(self.n), format='csr')
        self.rows, self.cols, self.steps = [], [], []
        for mask in range(self.masks):
            for r, coord in enumerate(self.coords):
                source = mask*self.n+r
                for axis in range(3):
                    for sign in [-1, 1]:
                        step = sign
                        if axis == 0 and (mask & 1) and coord[1:] == (4, 4):
                            replacement = {(4, 1): 2, (5, -1): 2, (6, 1): -2, (7, -1): -2}
                            step = replacement.get((coord[0], sign), sign)
                        target = list(coord)
                        target[axis] += step
                        shift = target[axis]//ell if axis == 0 else 0
                        target[axis] %= ell
                        new_mask = self.translate_mask(mask, shift)
                        self.rows.append(new_mask*self.n+self.lookup[tuple(target)])
                        self.cols.append(source)
                        displacement = [0, 0, 0]
                        displacement[axis] = step
                        self.steps.append(displacement)
        self.rows, self.cols = np.array(self.rows), np.array(self.cols)
        self.steps = np.array(self.steps)
        self.H0 = self.hamiltonian(np.zeros(3)).real.tocsr()
        assert sp.linalg.norm(self.H0-self.H0.T) < 1e-12
        assert np.linalg.norm(self.H0@self.g) < 1e-12
        assert abs(np.linalg.norm(self.g)-1) < 1e-12

    def translate_mask(self, mask, shift):
        return sum(((mask >> ((bit+shift) % self.cells)) & 1) << bit for bit in range(self.cells))

    def hamiltonian(self, k):
        hopping = sp.csr_matrix((-self.kappa*np.exp(1j*(self.steps@np.asarray(k))),
                                (self.rows, self.cols)), shape=(self.dim, self.dim))
        return self.geometry+6*self.kappa*sp.eye(self.dim, format='csr')+hopping

    def derivatives(self):
        first = sp.csr_matrix((-1j*self.kappa*self.steps[:, 0], (self.rows, self.cols)),
                              shape=(self.dim, self.dim))
        second = sp.csr_matrix((self.kappa*self.steps[:, 0]**2, (self.rows, self.cols)),
                               shape=(self.dim, self.dim))
        return first, second

    def audit(self):
        delta = min(self.omega, self.kappa*np.sin(np.pi/self.ell)**2)
        first, second = self.derivatives()
        f = first@self.g
        assert abs(np.vdot(self.g, f)) < 1e-12
        assert abs(np.vdot(f, f).real-20*self.kappa**2*self.p/self.n) < 1e-12
        regular = LinearOperator((self.dim, self.dim),
                                 matvec=lambda v: self.H0@v+self.g*np.vdot(self.g, v), dtype=complex)
        invdiag = 1/(self.H0.diagonal()+self.g**2)
        preconditioner = LinearOperator((self.dim, self.dim), matvec=lambda v: invdiag*v, dtype=complex)
        solved, info = cg(regular, f, M=preconditioner, rtol=1e-11, atol=1e-13, maxiter=6000)
        assert info == 0
        residual = float(np.linalg.norm(regular@solved-f))
        assert residual < 1e-10
        diamagnetic = float(np.vdot(self.g, second@self.g).real/2)
        assert abs(diamagnetic-self.kappa*(1+6*self.p/self.n)) < 1e-12
        correction = float(np.vdot(f, solved).real)
        Dx = diamagnetic-correction
        assert self.kappa/4 <= Dx <= 4*self.kappa
        spectrum = np.sort(eigsh(self.H0, k=3, which='SA', tol=1e-10, return_eigenvectors=False))
        assert abs(spectrum[0]) < 1e-10 and spectrum[1] >= delta-1e-10
        rows = []
        analytic_radius = .5*np.log1p(delta/(24*self.kappa))
        remainder_constant = delta/analytic_radius**4
        for q in [.04, .02, .01, .0005]:
            H = self.hamiltonian([q, 0, 0])
            assert sp.linalg.norm(H-H.conj().T) < 1e-12
            value = float(eigsh(H, k=1, which='SA', tol=1e-11,
                               v0=self.g.astype(complex), return_eigenvectors=False)[0])
            reference = 2*(1-np.cos(q))
            assert self.kappa*reference/4 <= value+1e-10 <= 4*self.kappa*reference+1e-10
            if q <= analytic_radius/2:
                assert abs(value-Dx*q*q) <= remainder_constant*q**4+1e-12
            rows.append(dict(momentum=q, energy=value, energy_over_q_squared=value/q**2,
                             quadratic_coefficient=Dx, quadratic_remainder=value-Dx*q*q,
                             within_conservative_analytic_radius=bool(q <= analytic_radius/2)))
        assert abs(rows[-1]['energy_over_q_squared']-Dx) < 2e-5
        # Transverse dispersion is an exact eigenvector identity, not a fit.
        transverse = self.hamiltonian([0., .03, -.02])
        transverse_energy = 2*self.kappa*(2-np.cos(.03)-np.cos(.02))
        transverse_residual = float(np.linalg.norm(transverse@self.g-transverse_energy*self.g))
        assert transverse_residual < 1e-12
        return dict(cells=self.cells, vertices=self.cells*self.n, fiber_dimension=self.dim,
                    geometry_gap=self.omega, uniform_fiber_gap_lower_bound=delta,
                    first_three_fiber_energies=spectrum.tolist(), active_probability=self.p,
                    diamagnetic_coefficient=diamagnetic, resolvent_correction=correction,
                    effective_Dx=Dx, effective_Dy=self.kappa, effective_Dz=self.kappa,
                    conservative_analytic_radius=analytic_radius, uniform_quartic_constant=remainder_constant,
                    poisson_residual=residual, transverse_eigenvector_residual=transverse_residual,
                    band_rows=rows)


def verify_fiber_compression(fiber):
    assert fiber.cells == 2
    ell, n = fiber.ell, fiber.n
    coords, reference = rectangular_torus((2*ell, ell, ell))
    lookup = {v: i for i, v in enumerate(coords)}
    switches = [tuple(lookup[(cell*ell+4+x, 4, 4)] for x in range(4)) for cell in range(2)]
    graphs = []
    for mask in range(4):
        adj = [set(v) for v in reference]
        for bit, p in enumerate(switches):
            if mask & (1 << bit):
                flip_in_place(adj, p)
        graphs.append(adj)
    full = sp.kron(sp.csr_matrix(fiber.bitH), sp.eye(2*n), format='csr')
    full += fiber.kappa*sp.block_diag([6*sp.eye(2*n)-adjacency_matrix(adj) for adj in graphs], format='csr')
    rows, cols = [], []
    for mask in range(4):
        for r, coord in enumerate(fiber.coords):
            for shift in range(2):
                lab_mask = fiber.translate_mask(mask, -shift)
                lab_coord = (coord[0]+shift*ell, coord[1], coord[2])
                rows.append(lab_mask*(2*n)+lookup[lab_coord])
                cols.append(mask*n+r)
    embedding = sp.csr_matrix((np.ones(len(rows))/np.sqrt(2), (rows, cols)), shape=(8*n, 4*n))
    assert sp.linalg.norm(embedding.T@embedding-sp.eye(4*n)) < 1e-12
    residual = float(sp.linalg.norm(full@embedding-embedding@fiber.H0))
    assert residual < 1e-10
    return dict(full_joint_dimension=8*n, invariant_fiber_dimension=4*n,
                intertwining_residual=residual,
                scope='Exact cell-translation quotient tested against the full two-cell joint Hamiltonian, up to roundoff.')


def counting_and_scaling():
    rows = []
    for L in [32, 64, 128]:
        q = 2*np.pi*np.arange(L)/L
        one = 2*(1-np.cos(q))
        eigenvalues = (one[:, None, None]+one[None, :, None]+one[None, None, :]).ravel()
        counts = []
        for E in [.05, .1, .2]:
            counts.append(dict(E=E, normalized_count=float(np.mean(eigenvalues <= E)),
                               leading_three_dimensional_count=E**1.5/(6*np.pi**2)))
        gap = 4*np.sin(np.pi/L)**2
        assert 16/L**2 <= gap+1e-15 <= 4*np.pi**2/L**2+1e-15
        rows.append(dict(side=L, first_reference_gap=gap, gap_times_side_squared=gap*L*L, counts=counts))
    return dict(reference_counts=rows, joint_gap_lower='min(Omega,kappa*lambda1(L0)/4)',
                joint_gap_upper='4*kappa*lambda1(L0)',
                low_energy_count_sandwich='N_L0(E/(4*kappa)) <= N_H(E) <= N_L0(4*E/kappa), E<Omega',
                nontrivial_low_band_time_scaling='t_micro=t_macro/a^2',
                linear_time_scaling_result='The shifted low-band propagator tends to the identity.')


def main():
    root = Path(__file__).resolve().parents[1]
    fibers = [QuantumFiber(cells=cells) for cells in [1, 2]]
    report = dict(exact_forms=exact_forms(), quantum_bands=[f.audit() for f in fibers],
                  fiber_compression=verify_fiber_compression(fibers[1]),
                  counting_and_scaling=counting_and_scaling())
    names = ['COLLECTIVE_SPACETIME_TEST.md', 'scripts/collective_spacetime_audit.py',
             'UnifiedTheory/Audit/KFCausalCollectiveSpacetime.lean',
             'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md', 'scripts/projected_geometry_audit.py',
             'ENERGETIC_PROBE_SECTOR.md', 'scripts/energetic_probe_audit.py',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'WEYL_WALK_CONTINUUM.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('Spatial spectral recovery and the low one-probe band of the supplied quantum '
                       'switch carrier. The continuum is Schroedinger; background/dimension selection, '
                       'internal time, a common Lorentzian matter cone, and Einstein dynamics remain open.')
    (root/'data/collective_spacetime_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
