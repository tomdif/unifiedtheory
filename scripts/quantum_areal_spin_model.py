#!/usr/bin/env python3
"""Finite spin realization of a proposed homogeneous reduced areal model.

This is a specified quantization of the reduced target, not a derivation
of gravitational constraints from the original spin Hamiltonian. Three
active flavors carry log(c), the polarized geometry field, and scalar
matter. Other excitation flavors can be retained as spectators.
"""
from __future__ import annotations

from dataclasses import dataclass
import math

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla
from scipy.special import gammaln
from scipy.stats import poisson

from holomorphic_tensor_phase_audit import finite_operators


@dataclass(frozen=True)
class Parameters:
    R: int
    hbar: float = 0.05
    correction: str = 'second_order'
    mass2: float = 0.5
    quartic: float = 0.1
    vacuum: float = 0.0
    flavors: int = 3
    functional_order: int | None = None


class ArealSpinModel:
    def __init__(self, params):
        self.params = p = params
        if p.R < 1 or p.hbar <= 0 or p.flavors < 3:
            raise ValueError('Positive capacity and hbar, and at least three flavors, are required.')
        if min(p.mass2, p.quartic, p.vacuum) < 0:
            raise ValueError('This positive-Hamiltonian candidate uses nonnegative potential coefficients.')
        if p.functional_order is not None and (p.functional_order < 2 or p.functional_order % 2):
            raise ValueError('The polynomial option uses a positive even Taylor order.')
        self.states, ann = finite_operators(p.flavors, p.flavors, p.R, p.R)
        self.states = np.asarray(self.states)
        self.dim = len(self.states)
        self.number = self.states.sum(axis=1)
        x = (self.number-1)/p.R
        factors = {'bare':np.ones(self.dim), 'first_order':1+x/2,
                   'second_order':1+x/2+3*x*x/8, 'exact':1/np.sqrt(1-x)}
        if p.correction not in factors:
            raise ValueError('Unknown spin amplitude correction.')
        self.ann = [A @ sp.diags(factors[p.correction]) for A in ann[:3]]
        scale = math.sqrt(p.hbar/2)
        coord = [scale*(A+A.T) for A in self.ann]
        momentum = [-1j*scale*(A-A.T) for A in self.ann]
        self.S, self.Q, self.phi = coord
        self.Ps, self.P, self.pi = momentum
        self._clock_matrices()
        ED = self.expLhalf @ self.inverseHalf
        self.static_terms = [self.clockHalf/math.sqrt(2),
                             (self.P @ self.inverseHalf)/math.sqrt(2),
                             (self.pi @ self.inverseHalf)/math.sqrt(2)]
        self.growing_terms = []
        if p.mass2:
            self.growing_terms.append(math.sqrt(p.mass2/2)*(self.phi @ ED))
        if p.quartic:
            self.growing_terms.append(math.sqrt(p.quartic/4)*(self.phi @ self.phi @ ED))
        if p.vacuum:
            self.growing_terms.append(math.sqrt(p.vacuum)*ED)
        self.static_adjoints = [A.conj().T.tocsr() for A in self.static_terms]
        self.growing_adjoints = [A.conj().T.tocsr() for A in self.growing_terms]
        self.static_trace = sum(float(np.sum(abs(A.data)**2)) for A in self.static_terms)
        self.growing_trace = sum(float(np.sum(abs(A.data)**2)) for A in self.growing_terms)

    def _clock_matrices(self):
        def half_exp(values, sign=1):
            x = sign*values/2
            order = self.params.functional_order
            if order is None:
                return np.exp(x)
            result = np.ones_like(x)
            term = np.ones_like(x)
            for k in range(1, order+1):
                term = term*x/k
                result += term
            return result

        groups = {}
        for i, state in enumerate(self.states):
            groups.setdefault(tuple(state[1:]), []).append(i)
        pieces = {key:([], [], []) for key in ['C','clockHalf','inverseHalf','L','expLhalf']}
        cache = {}
        for rest, indices in groups.items():
            indices = sorted(indices, key=lambda i:self.states[i, 0])
            rest_total = sum(rest)
            if rest_total not in cache:
                S = self.S[indices][:, indices].toarray()
                Ps = self.Ps[indices][:, indices].toarray()
                eig, vec = la.eigh(S)

                def spectral(f):
                    return (vec*f(eig)) @ vec.conj().T

                F = spectral(half_exp)
                C = F.conj().T @ F
                D = spectral(lambda x:half_exp(x,-1))
                Cinv = D @ D
                L = (Cinv @ Ps+Ps @ Cinv)/2
                eigL, vecL = la.eigh(L)
                EL = (vecL*half_exp(eigL)) @ vecL.conj().T
                cache[rest_total] = dict(C=C, clockHalf=F, inverseHalf=D, L=L, expLhalf=EL)
            rr, cc = np.meshgrid(indices, indices, indexing='ij')
            for key, block in cache[rest_total].items():
                row, col, val = pieces[key]
                row.extend(rr.ravel()); col.extend(cc.ravel()); val.extend(block.ravel())
        for key, (row, col, val) in pieces.items():
            setattr(self, key, sp.csr_matrix((val, (row, col)), shape=(self.dim, self.dim)))

    @staticmethod
    def _gram_apply(terms, adjoints, state):
        return sum((At @ (A @ state) for A, At in zip(terms, adjoints)),
                   np.zeros_like(state, dtype=complex))

    def apply_static(self, state):
        return self._gram_apply(self.static_terms, self.static_adjoints, state)

    def apply_growing(self, state):
        return self._gram_apply(self.growing_terms, self.growing_adjoints, state)

    def apply_H(self, time, state):
        return self.apply_static(state)+np.exp(2*time)*self.apply_growing(state)

    def matrix(self, time):
        result = sp.csr_matrix((self.dim, self.dim), dtype=complex)
        for scale, terms in [(1.,self.static_terms),(np.exp(2*time),self.growing_terms)]:
            for A in terms:
                result += scale*(A.conj().T @ A)
        return result

    def coherent_state(self, centers=(0.,0.,0.1,0.2,0.3,0.1)):
        s0, ps0, q0, p0, phi0, pi0 = centers
        alpha = np.array([s0+1j*ps0,q0+1j*p0,phi0+1j*pi0])/math.sqrt(2*self.params.hbar)
        psi = np.ones(self.dim, dtype=complex)*np.exp(-np.sum(abs(alpha)**2)/2)
        for a in range(3):
            psi *= alpha[a]**self.states[:, a]*np.exp(-gammaln(self.states[:, a]+1)/2)
        if self.params.flavors > 3:
            psi[np.any(self.states[:, 3:] != 0, axis=1)] = 0
        tail = float(poisson.sf(self.params.R, np.sum(abs(alpha)**2)))
        assert abs(np.vdot(psi, psi).real-(1-tail)) < 2e-13
        psi /= la.norm(psi)
        return psi, tail

    def evolve(self, state, end, steps):
        """Unitary exponential midpoint steps for H(t)=H0+exp(2t)V."""
        if steps < 1 or int(steps) != steps:
            raise ValueError('Evolution requires a positive integer step count.')
        steps = int(steps)
        dt = end/steps
        psi = state.copy()
        for j in range(steps):
            t = (j+0.5)*dt
            scale = -1j*dt/self.params.hbar
            operator = sla.LinearOperator((self.dim,self.dim), dtype=complex,
                matvec=lambda x, t=t, scale=scale:scale*self.apply_H(t,x),
                rmatvec=lambda x, t=t, scale=scale:scale.conjugate()*self.apply_H(t,x),
                matmat=lambda x, t=t, scale=scale:scale*self.apply_H(t,x))
            trace = scale*(self.static_trace+np.exp(2*t)*self.growing_trace)
            psi = sla.expm_multiply(operator, psi, traceA=trace)
        return psi

    def diagnostics(self, time, state):
        Hpsi = self.apply_H(time, state)
        Cpsi = self.C @ state
        rate = float((1j/self.params.hbar*(np.vdot(Hpsi,Cpsi)-np.vdot(Cpsi,Hpsi))).real)
        potential = float((np.exp(2*time)*np.vdot(state,self.apply_growing(state))).real)
        return dict(norm=float(la.norm(state)), clock=float(np.vdot(state,Cpsi).real),
                    clock_rate=rate, potential_energy=potential,
                    clock_rate_defect=abs(rate-potential),
                    energy=float(np.vdot(state,Hpsi).real),
                    longitudinal=float(np.vdot(state,self.L @ state).real),
                    scalar=float(np.vdot(state,self.phi @ state).real),
                    top_two_probability=float(np.sum(abs(state[self.number >= self.params.R-1])**2)))


class ArealSpinLattice:
    """Finite supplied graph with positive common-coefficient bond gradients.

    This discretizes the reduced Hamiltonian. It does not enforce an
    exact lattice version of the remaining spatial constraint.
    """
    def __init__(self, local, sites, edges):
        edges = tuple(edges)
        if sites < 1 or any(x == y or not (0 <= x < sites and 0 <= y < sites) for x,y in edges):
            raise ValueError('Invalid graph.')
        self.local, self.sites, self.edges = local, sites, tuple(edges)
        self.dim = local.dim**sites
        self.params = local.params
        eye = sp.eye(local.dim, format='csr')

        def embed(A, site):
            result = sp.csr_matrix([[1.]])
            for j in range(sites):
                result = sp.kron(result, A if j == site else eye, format='csr')
            return result

        self.clocks = [embed(local.C,j) for j in range(sites)]
        self.static_terms = [embed(A,j) for j in range(sites) for A in local.static_terms]
        self.growing_terms = [embed(A,j) for j in range(sites) for A in local.growing_terms]
        self.gradient_terms = []
        for x,y in edges:
            for field in [local.Q,local.phi]:
                difference = embed(field,y)-embed(field,x)
                for endpoint in [x,y]:
                    # 1/4*(1/c_x+1/c_y)*(field_y-field_x)^2 in the
                    # commuting symbol; gravity and matter use equal weights.
                    term = (difference @ embed(local.inverseHalf,endpoint))/2
                    self.gradient_terms.append(term)
        self.growing_terms += self.gradient_terms
        self.static_adjoints = [A.conj().T.tocsr() for A in self.static_terms]
        self.growing_adjoints = [A.conj().T.tocsr() for A in self.growing_terms]
        self.static_trace = sum(float(np.sum(abs(A.data)**2)) for A in self.static_terms)
        self.growing_trace = sum(float(np.sum(abs(A.data)**2)) for A in self.growing_terms)

    _gram_apply = staticmethod(ArealSpinModel._gram_apply)
    apply_static = ArealSpinModel.apply_static
    apply_growing = ArealSpinModel.apply_growing
    apply_H = ArealSpinModel.apply_H
    matrix = ArealSpinModel.matrix
    evolve = ArealSpinModel.evolve
