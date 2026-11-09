#!/usr/bin/env python3
"""Optional epsilon-regularized full six-mode exponential candidate.

The spatial Jordan reconstruction, matter fields and time dependence are
inherited from the specified constrained model. Only its neutral clock
momentum datum changes to sym((C+epsilon I)^-1 Ps). The original model's
default is unchanged. No infinite-capacity limit is assumed.
"""
import numpy as np
import scipy.linalg as la
import scipy.sparse as sp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


class RegularizedConstraintSpinModel(ConstraintReducedSpinModel):
    def __init__(self, params: Parameters, epsilon: float):
        if not np.isfinite(epsilon) or epsilon < 0:
            raise ValueError('A finite nonnegative longitudinal regulator is required.')
        if params.functional_order is not None:
            raise ValueError('This candidate uses exact matrix exponentials.')
        self.epsilon = float(epsilon)
        super().__init__(params)

    def _clock_matrices(self):
        # Construct the revised datum directly; do not first exponentiate
        # the unregularized longitudinal block, which may be very large.
        groups = {}
        for i,state in enumerate(self.states):
            groups.setdefault(tuple(state[1:]),[]).append(i)
        pieces = {key:([],[],[]) for key in ['C','clockHalf','inverseHalf','mobility','L']}
        cache = {}
        for rest,indices in groups.items():
            indices = sorted(indices,key=lambda i:self.states[i,0])
            rest_total = sum(rest)
            if rest_total not in cache:
                S = self.S[indices][:,indices].toarray()
                Ps = self.Ps[indices][:,indices].toarray()
                values,U = la.eigh(S)
                def spectral(values):
                    return (U*values)@U.conj().T
                F = spectral(np.exp(values/2))
                C = F.conj().T@F
                D = spectral(np.exp(-values/2))
                mobility = spectral(1/(np.exp(values)+self.epsilon))
                L = (mobility@Ps+Ps@mobility)/2
                cache[rest_total] = dict(C=C,clockHalf=F,inverseHalf=D,mobility=mobility,L=L)
            rr,cc = np.meshgrid(indices,indices,indexing='ij')
            for key,block in cache[rest_total].items():
                row,col,val = pieces[key]
                row.extend(rr.ravel());col.extend(cc.ravel());val.extend(block.ravel())
        for key,(row,col,val) in pieces.items():
            setattr(self,key,sp.csr_matrix((val,(row,col)),shape=(self.dim,self.dim)))
