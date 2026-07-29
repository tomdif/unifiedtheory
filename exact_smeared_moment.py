#!/usr/bin/env python3
"""Exact second moment of the ASS smeared weights (test 4b).

f(n,eps) = (1-e)^n [1 - 9en/(1-e) + 8e^2 n(n-1)/(1-e)^2 - (4/3)e^3 n^(3)/(1-e)^3]
Mean identity (verified symbolically): E[(1-e)^N f-bracket] = f4D(e*xi) EXACT.
Second moment via E[c^N N^(k)] = (c xi)^k e^{-(1-c)xi}, c = (1-e)^2:
  M(eps) := M[eps^2 E f^2 (eps .)](1/2) = (105/4) sqrt(pi) eps^{3/2}
              (eps^2 + 2 eps + 3) / (2 - eps)^{13/2}
Checks: eps->0: (315/512) sqrt2 sqrt(pi) eps^{3/2}  [= LEAN mesoscale_suppression]
        eps=1 : (315/2) sqrt(pi)                    [= LEAN f4Dsq_mass_half]
Correction factor: 1 + (47/6) eps + O(eps^2).
"""
import sympy as sp
e = sp.symbols('epsilon', positive=True)
M = sp.Rational(105,4)*sp.sqrt(sp.pi)*e**sp.Rational(3,2)*(e**2+2*e+3)/(2-e)**sp.Rational(13,2)
lead = sp.limit(M/(e**sp.Rational(3,2)*sp.sqrt(sp.pi)), e, 0)
print("eps->0 coeff:", lead, "== 315 sqrt2/512:", sp.simplify(lead - sp.Rational(315,512)*sp.sqrt(2)) == 0)
sharp = M.subs(e, 1)
print("eps=1:", sp.simplify(sharp), "== (315/2)sqrt(pi):", sp.simplify(sharp - sp.Rational(315,2)*sp.sqrt(sp.pi)) == 0)
ser = sp.series(M/(e**sp.Rational(3,2)*sp.sqrt(sp.pi)*sp.Rational(315,512)*sp.sqrt(2)), e, 0, 2)
print("correction series:", sp.simplify(ser))
