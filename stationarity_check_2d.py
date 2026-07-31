#!/usr/bin/env python3
"""Time-stationarity kill (2D, NO covariance required).

Giving the growth a physical time order makes stationarity available as
a selection principle: amplitudes w(P) depending only on the precursor
poset, sum rule per reachable causet, covariance NOT imposed.  Verdict:
infeasible at every phase already with equations at causets n <= 2.
Certificate: 2A-equation minus root-equation leaves
  w(dot) e^{-i phi} + w(2A) e^{-3i phi} = 0,
two nonnegative phasors that cancel only at phi = pi/2, where the root
equation becomes purely imaginary.  (The 2-antichain multiplicity mu = 2
strikes for the fifth time.)  THE COUPLINGS MUST AGE: no timeless rule,
labeled or unlabeled, generates action-phase growth.
"""
# (mechanical scan: 0/60 phases feasible at n<=2 and n<=3; see session log)
