#!/usr/bin/env python3
"""Specified reduced quantum candidate with an exact residual constraint.

The local spatial constraint is solved by a positive-clock Jordan inverse.
The spatial average is exact translation-charge dephasing; its zero-charge
sector is preserved. This changes the earlier supplied-graph model to a
nonlocal Fourier reduction, not a derived microscopic gravitational phase.
"""
import math

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla
from scipy.special import gammaln

from holomorphic_tensor_phase_audit import finite_operators
from quantum_areal_spin_model import ArealSpinModel, Parameters


class ConstraintReducedSpinModel:
    """Six flavors: clock, Q(+,-), phi(+,-), and homogeneous phi."""
    _clock_matrices = ArealSpinModel._clock_matrices

    def __init__(self, params):
        p = self.params = params
        if p.flavors != 6 or p.R < 1 or p.hbar <= 0:
            raise ValueError('This reduction requires six flavors, positive R and hbar.')
        if min(p.mass2,p.quartic,p.vacuum) < 0:
            raise ValueError('Nonnegative potential coefficients are required.')
        if p.functional_order is not None and (p.functional_order < 2 or p.functional_order % 2):
            raise ValueError('Use an even positive Taylor order or exact matrix functions.')
        states, ann = finite_operators(6,6,p.R,p.R)
        self.states = np.asarray(states)
        self.number = self.states.sum(axis=1)
        self.dim = len(states)
        x = (self.number-1)/p.R
        if p.correction == 'exact':
            f = 1/np.sqrt(1-x)
        elif p.correction == 'second_order':
            f = 1+x/2+3*x*x/8
        elif p.correction == 'bare':
            f = np.ones(self.dim)
        else:
            raise ValueError('Unknown amplitude correction.')
        self.ann = [A@sp.diags(f) for A in ann]
        self.charge = self.states@np.array([0,1,-1,1,-1,0])
        self.charge_difference = self.charge[:,None]-self.charge[None,:]
        self.same_charge = self.charge_difference == 0
        self.physical = np.flatnonzero(self.charge==0)
        scale = math.sqrt(p.hbar/2)

        def pair(A):
            return scale*(A+A.conj().T), -1j*scale*(A-A.conj().T)

        self.S,self.Ps = pair(self.ann[0])
        self._clock_matrices()
        self.C,self.Lbar,self.D,self.F = [A.toarray() for A in
            [self.C,self.L,self.inverseHalf,self.clockHalf]]
        ac = (self.ann[1]+self.ann[2])/math.sqrt(2)
        ass = (self.ann[1]-self.ann[2])/(1j*math.sqrt(2))
        qc,pc = pair(ac); qs,ps = pair(ass)
        ac = (self.ann[3]+self.ann[4])/math.sqrt(2)
        ass = (self.ann[3]-self.ann[4])/(1j*math.sqrt(2))
        fc,pic = pair(ac); fs,pis = pair(ass)
        f0,pi0 = pair(self.ann[5])
        self.Q = (math.sqrt(2)*qc).toarray()
        self.P = (math.sqrt(2)*pc).toarray()
        self.Qx = (math.sqrt(2)*qs).toarray()
        self.phi = (f0+math.sqrt(2)*fc).toarray()
        self.pi = (pi0+math.sqrt(2)*pic).toarray()
        self.phix = (math.sqrt(2)*fs).toarray()
        raw_source = self.P@self.Qx+self.pi@self.phix
        self.source = (raw_source+raw_source.conj().T)/2
        self.mean_source = self.source*self.same_charge
        primitive = np.zeros_like(self.source)
        np.divide(self.source,1j*self.charge_difference,out=primitive,where=~self.same_charge)

        # This inverse solves (C X + X C)/2=primitive exactly. Simply
        # symmetrizing C^{-1} primitive would leave a commutator defect.
        self.L = self.Lbar+la.solve_sylvester(self.C,self.C,2*primitive)
        self.Lx = 1j*self.charge_difference*self.L
        self.constraint = self.source-(self.C@self.Lx+self.Lx@self.C)/2
        if p.functional_order is None:
            E = la.expm(self.L/2)
        else:
            E = np.eye(self.dim,dtype=complex)
            term = E.copy()
            for k in range(1,p.functional_order+1):
                term = term@self.L/(2*k)
                E += term
        ED = E@self.D
        static_terms = [self.F/math.sqrt(2), self.P@self.D/math.sqrt(2),
                        self.pi@self.D/math.sqrt(2)]
        gradient_terms = [self.Qx@self.D/math.sqrt(2),self.phix@self.D/math.sqrt(2)]
        potential_terms = [math.sqrt(p.mass2/2)*self.phi@ED,
                           math.sqrt(p.quartic/4)*self.phi@self.phi@ED,
                           math.sqrt(p.vacuum)*ED]

        def gram_sum(terms):
            return sum((A.conj().T@A for A in terms),np.zeros((self.dim,self.dim),complex))

        self.seed_static = gram_sum(static_terms)
        self.seed_growing = gram_sum(gradient_terms+potential_terms)
        self.static = self.seed_static*self.same_charge
        self.growing = self.seed_growing*self.same_charge
        self.gradient = gram_sum(gradient_terms)*self.same_charge
        self.potential = gram_sum(potential_terms)*self.same_charge
        ix = np.ix_(self.physical,self.physical)
        self.physical_static,self.physical_growing = self.static[ix],self.growing[ix]

    def matrix(self,time,physical=False):
        if physical:
            return self.physical_static+np.exp(2*time)*self.physical_growing
        return self.static+np.exp(2*time)*self.growing

    def physical_packet(self,alpha=(0.,0.3+0.1j,0.3+0.1j,0.25,0.25,0.7+0.1j)):
        psi = np.ones(self.dim,dtype=complex)
        for j,a in enumerate(alpha):
            psi *= a**self.states[:,j]*np.exp(-gammaln(self.states[:,j]+1)/2)
        probability = float(la.norm(psi[self.physical])**2/la.norm(psi)**2)
        psi = psi[self.physical]
        return psi/la.norm(psi),probability

    def embed(self,state):
        full = np.zeros(self.dim,dtype=complex)
        full[self.physical] = state
        return full

    def evolve(self,state,end,steps):
        if steps < 1 or int(steps)!=steps:
            raise ValueError('Use a positive integer number of time steps.')
        psi = state.copy()
        dt = end/int(steps)
        for j in range(int(steps)):
            H = self.matrix((j+0.5)*dt,physical=True)
            psi = sla.expm_multiply(-1j*dt/self.params.hbar*H,psi)
        return psi
