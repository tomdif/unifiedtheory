#!/usr/bin/env python3
"""Exact checks linking the tensor parent to a nonlinear clock candidate.

SymPy checks are independent algebraic audits, not Lean proofs. The Lean
modules prove the real-symbol kernel and the variational-jet bracket.
"""
import json
from pathlib import Path

import sympy as s

from compact_tensor_constraint_audit import stencil_symbols


def tensor_symbol_bridge():
    (w, lattice_g, lattice_b, _, _), _ = stencil_symbols()
    t = s.symbols("tx ty tz", nonzero=True)
    v = [(u - 1/u)/s.I for u in t]
    x, y, z = s.symbols("vx vy vz", real=True)
    ell = x*x+y*y+z*z
    g = s.Matrix([[2*x, 0, 0], [0, 2*y, 0], [0, 0, 2*z],
                  [y, x, 0], [0, z, y], [z, 0, x]])
    b = s.Matrix([[x*x-ell, y*y-ell, z*z-ell, 2*x*y, 2*y*z, 2*z*x]])
    weight = s.diag(1, 1, 1, s.sqrt(2), s.sqrt(2), s.sqrt(2))
    phase = s.diag(t[0]**2, t[1]**2, t[2]**2,
                   t[0]*t[1], t[1]*t[2], t[2]*t[0])
    input_phase = s.diag(*(1/u for u in t))
    wave_sub = dict(zip((x, y, z), v))
    lattice_sub = {wi: ti**2 for wi, ti in zip(w, t)}
    assert (lattice_g.subs(lattice_sub) -
            s.I*phase*g.subs(wave_sub)*input_phase).applyfunc(s.simplify) == s.zeros(6, 3)
    assert (lattice_b.subs(lattice_sub) -
            b.subs(wave_sub)*phase.inv()).applyfunc(s.simplify) == s.zeros(1, 6)
    assert b*g == s.zeros(1, 3) or (b*g).applyfunc(s.expand) == s.zeros(1, 3)
    gf = weight*g
    bf = b*weight.inv()
    k = gf*gf.T+bf.T*bf
    constraints = s.Matrix([[x, 0, 0, y, 0, z], [0, y, 0, x, z, 0],
                            [0, 0, z, 0, y, x], [1, 1, 1, 0, 0, 0]])
    assert s.factor((constraints*weight.inv()**2*constraints.T).det()-ell**3/2) == 0
    h = s.Matrix(s.symbols("h0:6"))
    d = constraints[:3, :]*h
    beta = (b*h)[0]
    expected = s.Matrix([
        4*x*d[0]+(x*x-ell)*beta, 4*y*d[1]+(y*y-ell)*beta,
        4*z*d[2]+(z*z-ell)*beta, 2*(x*d[1]+y*d[0])+x*y*beta,
        2*(y*d[2]+z*d[1])+y*z*beta, 2*(z*d[0]+x*d[2])+z*x*beta])
    assert (weight.inv()*k*weight*h-expected).applyfunc(s.expand) == s.zeros(6, 1)
    return {
        "exact_laurent_staggering_identities": True,
        "exact_Lean_penalty_coordinate_match": True,
        "weighted_gram_determinant": "(vx^2+vy^2+vz^2)^3/2",
        "scope": "For t_i=exp(i*k_i/2), the phase matrices are unitary and v_i=2*sin(k_i/2). The source lattice penalty is unitarily equivalent to the Lean real symbol. This bridge is checked by SymPy, not yet formalized in Lean.",
    }


def nonlinear_clock():
    q = s.symbols("x y z", real=True)
    dq = s.symbols("dx dy dz", real=True)
    ddq = s.symbols("ddx ddy ddz", real=True)
    dddq = s.symbols("dddx dddy dddz", real=True)
    p = s.symbols("px py pz", real=True)
    dp = s.symbols("dpx dpy dpz", real=True)
    n, dn, ddn, m, dm, ddm = s.symbols("N dN ddN M dM ddM", real=True)
    a, b, lam = s.symbols("a b lambda", real=True)
    jets = dict(zip(q+dq+ddq+p+(n, dn, m, dm),
                    dq+ddq+dddq+dp+(dn, ddn, dm, ddm)))

    def d(f):
        return sum(s.diff(f, u)*du for u, du in jets.items())

    def partial(f, index):
        return d(f) if index == 1 else s.S.Zero

    metric = s.diag(*(s.exp(u) for u in q))
    inverse = metric.inv()
    gamma = [[[s.simplify(sum(inverse[k, l]*(partial(metric[l, j], i)+
               partial(metric[l, i], j)-partial(metric[i, j], l))/2
               for l in range(3))) for j in range(3)] for i in range(3)] for k in range(3)]
    ricci = s.Matrix(3, 3, lambda i, j: s.simplify(sum(
        partial(gamma[k][i][j], k)-partial(gamma[k][i][k], j)+sum(
            gamma[k][i][j]*gamma[l][k][l]-gamma[l][i][k]*gamma[k][j][l]
            for l in range(3)) for k in range(3))))
    curvature = s.simplify(s.trace(inverse*ricci))
    potential_jet = ddq[0]+ddq[2]+(dq[0]**2+dq[2]**2+
                    dq[0]*dq[2]-dq[1]*(dq[0]+dq[2]))/2
    assert s.simplify(curvature+s.exp(-q[1])*potential_jet) == 0
    e = s.exp(-sum(q)/2)
    f = s.exp((q[0]-q[1]+q[2])/2)
    kinetic = sum(pi**2 for pi in p)-lam*sum(p)**2
    hamiltonian = a*e*kinetic+b*f*potential_jet

    def euler(f, i):
        return s.diff(f, q[i])-d(s.diff(f, dq[i]))+d(d(s.diff(f, ddq[i])))

    bracket = s.expand(sum(euler(n*hamiltonian, i)*s.diff(m*hamiltonian, p[i])-
                           s.diff(n*hamiltonian, p[i])*euler(m*hamiltonian, i)
                           for i in range(3)))
    first = s.simplify(bracket.coeff(n).coeff(dm))
    second = s.simplify(bracket.coeff(n).coeff(ddm))
    assert s.simplify(bracket-first*(n*dm-m*dn)-second*(n*ddm-m*ddn)) == 0
    current = s.simplify(first-d(second))
    spatial_constraint = sum(pi*qi for pi, qi in zip(p, dq))-2*dp[1]
    trace_anomaly = 2*sum(dp)-sum(dq)*sum(p)
    expected = a*b*s.exp(-q[1])*(spatial_constraint-(2*lam-1)*trace_anomaly)
    assert s.simplify(current-expected) == 0
    assert s.simplify(current.subs(lam, s.Rational(1, 2))-
                      a*b*inverse[1, 1]*spatial_constraint) == 0

    def poisson(left, right):
        return sum(euler(left, i)*s.diff(right, p[i])-
                   s.diff(left, p[i])*euler(right, i) for i in range(3))

    spatial_n = n*sum(pi*qi for pi, qi in zip(p, dq))+2*dn*p[1]
    spatial_m = m*sum(pi*qi for pi, qi in zip(p, dq))+2*dm*p[1]
    assert s.simplify(poisson(spatial_n, spatial_m)-
                      (n*dm-m*dn)*spatial_constraint) == 0
    mixed_boundary = -n*m*a*e*kinetic-n*m*b*f*dq[0]*dq[2]/2-n*dm*b*f*(dq[0]+dq[2])
    assert s.simplify(poisson(spatial_n, m*hamiltonian)-
                      n*dm*hamiltonian-d(mixed_boundary)) == 0
    for i in range(3):
        assert s.diff(spatial_n, p[i]) == n*dq[i]+(2*dn if i == 1 else 0)
        assert s.simplify(-euler(spatial_n, i)-(n*dp[i]+dn*p[i])) == 0

    # A periodic, flat, divergence-free momentum witness. It is deliberately
    # tested before the TT quotient, where a clock algebra has content.
    u = s.symbols("u", real=True)
    witness = dict.fromkeys(q+dq+ddq+p+dp, 0)
    witness.update({p[0]: s.cos(u), dp[0]: -s.sin(u)})
    assert spatial_constraint.subs(witness) == 0
    w = -s.sin(u)  # N=1, M=cos(u), so N M'-M N'=-sin(u).
    integrated = s.simplify(s.integrate(current.subs(witness)*w, (u, 0, 2*s.pi)))
    assert s.simplify(integrated-2*s.pi*a*b*(1-2*lam)) == 0
    # A supplied local coordinate-only potential cannot change this bracket.
    c = s.symbols("c", real=True)
    coordinate_cubic = c*(q[0]**3+q[0]*q[1]*q[2])
    amended = hamiltonian+coordinate_cubic
    amended_bracket = sum(euler(n*amended, i)*s.diff(m*amended, p[i])-
                         s.diff(n*amended, p[i])*euler(m*amended, i) for i in range(3))
    assert s.simplify(amended_bracket-bracket) == 0
    trace_value = s.simplify(kinetic.subs(lam, s.Rational(1, 2)).subs(dict.fromkeys(p, 1)))
    assert trace_value == -s.Rational(3, 2)
    return {
        "ricci_derived_from_Christoffel_symbols": True,
        "Euler_bracket_computed_from_density": True,
        "spatial_spatial_bracket": True,
        "spatial_normal_bracket_with_exact_boundary": True,
        "spatial_generator_metric_and_momentum_actions": True,
        "hamiltonian_density": str(hamiltonian),
        "bracket_current": str(expected),
        "DeWitt_lambda": "1/2",
        "inverse_metric_structure_function": "a*b*exp(-y)",
        "periodic_witness_spatial_constraint": 0,
        "periodic_witness_clock_bracket": str(integrated),
        "representative_ultralocal_cubic_bracket_unchanged": True,
        "unit_homogeneous_trace_kinetic_at_lambda_half": str(trace_value),
        "scope": "Nonlinear diagonal fields depending on one spatial coordinate, periodic smearing. A target continuum constraint ansatz; no claim of microscopic derivation, complete 3D constraint closure, quantum anomaly control, or stable spin realization.",
    }


def areal_reduction():
    """Derive and check all six original Hamilton equations in the gauge."""
    T, Q, L = q = s.symbols("T Q L", real=True)
    dT, dQ, dL = dq = s.symbols("dT dQ dL", real=True)
    ddT, ddQ, ddL = ddq = s.symbols("ddT ddQ ddL", real=True)
    dddq = s.symbols("dddT dddQ dddL", real=True)
    PT, P, PL = p = s.symbols("PT P PL", real=True)
    dPT, dP, dPL = dp = s.symbols("dPT dP dPL", real=True)
    n, dn, ddn = s.symbols("N dN ddN", real=True)
    a, b, c = s.symbols("a b c", positive=True)
    jets = dict(zip(q+dq+ddq+p+(n, dn), dq+ddq+dddq+dp+(dn, ddn)))

    def d(expr):
        return sum(s.diff(expr, var)*next_var for var, next_var in jets.items())

    def euler(expr, i):
        return s.diff(expr, q[i])-d(s.diff(expr, dq[i]))+d(d(s.diff(expr, ddq[i])))

    px, py, pz = (PT+P)/2, PL, (PT-P)/2
    kinetic = s.expand(px**2+py**2+pz**2-(px+py+pz)**2/2)
    assert kinetic == P**2/2+PL**2/2-PT*PL
    potential = s.expand(2*ddT+((dT+dQ)**2+(dT-dQ)**2+
                         (dT+dQ)*(dT-dQ)-2*dL*dT)/2)
    assert s.expand(potential-(2*ddT+3*dT**2/2+dQ**2/2-dL*dT)) == 0
    h = a*s.exp(-T-L/2)*kinetic+b*s.exp(T-L/2)*potential
    k = (b/a)*s.exp(2*T)
    physical = c/2+(P**2+k*dQ**2)/(2*c)
    lapse = s.exp(T+L/2)/(a*c)
    metric_spatial = P*dQ/c
    metric_time = -s.Rational(1, 2)+(P**2+k*dQ**2)/(2*c**2)
    energy_rate = k*(dP*dQ+P*ddQ)/c**2+k*dQ**2/c
    gauge = {dT: 0, ddT: 0, PL: -c, dPL: 0, PT: -physical,
             dL: metric_spatial, ddL: (dP*dQ+P*ddQ)/c,
             n: lapse, dn: lapse*dL/2, ddn: lapse*(ddL/2+dL**2/4)}

    def in_gauge(expr):
        # Simultaneous replacements preserve the fact that the lapse was
        # held independent while taking the Hamiltonian variation.
        expr = expr.subs(gauge, simultaneous=True)
        return s.simplify(expr.subs({dL: metric_spatial, ddL: (dP*dQ+P*ddQ)/c}))

    assert in_gauge(h) == 0
    assert s.simplify((PT*dT+P*dQ+PL*dL-2*dPL).subs(gauge, simultaneous=True)) == 0
    coordinate_rates = [1, P/c, metric_time]
    momentum_rates = [-energy_rate, k*ddQ/c, 0]
    for i in range(3):
        assert s.simplify(in_gauge(s.diff(n*h, p[i]))-coordinate_rates[i]) == 0
        assert s.simplify(in_gauge(-euler(n*h, i))-momentum_rates[i]) == 0
    compatibility = ((k*ddQ/c)*dQ+P*dP/c)/c-(P*dP+k*dQ*ddQ)/c**2
    assert s.simplify(compatibility) == 0
    assert s.simplify(s.diff(physical, P)*(k*ddQ/c)+
                      s.diff(physical, dQ)*(dP/c)+s.diff(physical, T)-energy_rate) == 0
    assert s.simplify((b/a).subs(b, 1/a)-1/a**2) == 0
    return {
        "canonical_area_change_of_variables": True,
        "gauge": "T=tau, P_L=-c<0, zero shift; retain the global L/c data",
        "physical_Hamiltonian_density": str(physical),
        "all_six_original_Hamilton_equations": True,
        "scalar_and_spatial_constraints": True,
        "metric_reconstruction_compatible": True,
        "energy_balance_with_time_dependent_source": True,
        "wave_metric_cone_agrees_when_a_times_b_equals_one": True,
        "periodic_obligation": "integral P*Q' ds=0; the local momentum divergence law preserves it for smooth periodic solutions",
        "scope": "Classical polarized diagonal sector only. Gauge admissibility is assumed, c is nonzero, homogeneous global data remain, and periodic reconstruction needs the global momentum condition. No microscopic emergence, general 3D reduction, PDE existence, or quantum implementation is claimed.",
    }


def main():
    report = {"tensor_symbol": tensor_symbol_bridge(), "diagonal_clock": nonlinear_clock(),
              "areal_reduction": areal_reduction()}
    path = Path(__file__).resolve().parents[1]/"data"/"diagonal_clock_dynamics_audit.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"all_exact_checks_passed": True, "report": str(path)}, indent=2))


if __name__ == "__main__":
    main()
