#!/usr/bin/env python3
"""Independent canonical checks for a proposed gravity/matter model revision.

Exact symbolic Euler brackets use exponential metric components rather
than the polynomial coefficient jets in Lean. The final evolution test is
homogeneous and classical; it is not a spin simulation or a TOE proof.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
import sympy as s


def constraint_algebra():
    q = s.symbols('x y z phi', real=True)
    dq = s.symbols('dx dy dz dphi', real=True)
    ddq = s.symbols('ddx ddy ddz ddphi', real=True)
    dddq = s.symbols('dddx dddy dddz dddphi', real=True)
    p = s.symbols('px py pz pi', real=True)
    dp = s.symbols('dpx dpy dpz dpi', real=True)
    N, dN, ddN, M, dM, ddM = s.symbols('N dN ddN M dM ddM', real=True)
    a, b, lam, kap, gam, mass2, quartic, vacuum = s.symbols(
        'a b lam kap gam mass2 quartic vacuum', real=True)
    jets = dict(zip(q+dq+ddq+p+(N, dN, M, dM),
                    dq+ddq+dddq+dp+(dN, ddN, dM, ddM)))

    def D(expr):
        return sum(s.diff(expr, var)*velocity for var, velocity in jets.items())

    def euler(expr, i):
        return s.diff(expr, q[i])-D(s.diff(expr, dq[i]))+D(D(s.diff(expr, ddq[i])))

    def bracket(F, G):
        return s.expand(sum(euler(F, i)*s.diff(G, p[i])-
                            s.diff(F, p[i])*euler(G, i) for i in range(4)))

    x, y, z, phi = q
    e, f, vol = s.exp(-(x+y+z)/2), s.exp((x-y+z)/2), s.exp((x+y+z)/2)
    kin = sum(pi*pi for pi in p[:3])-lam*sum(p[:3])**2
    curv = ddq[0]+ddq[2]+(dq[0]**2+dq[2]**2+dq[0]*dq[2]-dq[1]*(dq[0]+dq[2]))/2
    V = mass2*phi**2/2+quartic*phi**4/4+vacuum
    HG = a*e*kin+b*f*curv
    HM = kap*e*p[3]**2/2+gam*f*dq[3]**2/2+vol*V
    H = HG+HM
    DG = sum(pi*qi for pi, qi in zip(p[:3], dq[:3]))-2*dp[1]
    DM = p[3]*dq[3]
    W = N*dM-M*dN
    anomaly = 2*sum(dp[:3])-sum(dq[:3])*sum(p[:3])
    normal = bracket(N*H, M*H)
    first = s.simplify(normal.coeff(N).coeff(dM))
    second = s.simplify(normal.coeff(N).coeff(ddM))
    assert s.simplify(normal-first*W-second*(N*ddM-M*ddN)) == 0
    expected = e*f*(a*b*(DG-(2*lam-1)*anomaly)+kap*gam*DM)
    assert s.simplify(first-D(second)-expected) == 0
    assert s.simplify(bracket(N*HG, M*HM)+bracket(N*HM, M*HG)) == 0
    assert s.simplify(bracket(N*HM, M*HM)-kap*gam*e*f*DM*W) == 0

    DN = N*sum(pi*qi for pi, qi in zip(p, dq))+2*dN*p[1]
    DMsmear = M*sum(pi*qi for pi, qi in zip(p, dq))+2*dM*p[1]
    assert s.simplify(bracket(DN, DMsmear)-W*(DG+DM)) == 0
    boundaryG = -N*M*a*e*kin-N*M*b*f*dq[0]*dq[2]/2-N*dM*b*f*(dq[0]+dq[2])
    boundaryM = N*M*(-kap*e*p[3]**2/2+gam*f*dq[3]**2/2-vol*V)
    assert s.simplify(bracket(DN, M*H)-N*dM*H-D(boundaryG+boundaryM)) == 0
    bare_defect = s.simplify(bracket(DN, M*V)-N*dM*V-D(-N*M*V))
    assert s.simplify(bare_defect-dN*M*V) == 0
    u = s.symbols('u', real=True)
    periodic_defect = s.integrate(s.cos(u)**2, (u, 0, 2*s.pi))
    assert periodic_defect == s.pi
    print('Exact coupled canonical brackets and bare-potential counterexample passed.', flush=True)
    return dict(normal_bracket_with_divergence=True, cross_terms_cancel=True,
                spatial_spatial=True, spatial_normal_with_divergence=True,
                current=str(expected), selection='lambda=1/2 and kappa*gamma=a*b',
                potential_parameters_selected=False, bare_potential_defect=str(bare_defect),
                periodic_bare_potential_defect='pi for V=1, N=sin(s), M=cos(s)')


def homogeneous_reduction():
    T, Q, L, phi, PT, P, PL, pi = s.symbols('T Q L phi PT P PL pi', real=True)
    a, kap, c = s.symbols('a kap c', positive=True)
    mass2, quartic, vacuum = s.symbols('mass2 quartic vacuum', real=True)
    e, vol = s.exp(-T-L/2), s.exp(T+L/2)
    V = mass2*phi**2/2+quartic*phi**4/4+vacuum
    H = a*e*(P**2/2+PL**2/2-PT*PL)+kap*e*pi**2/2+vol*V
    E = P**2+kap*pi**2/a
    W = s.exp(2*T+L)*V/a
    reduced = c/2+(E+2*W)/(2*c)
    gauge = {PL:-c, PT:-reduced}
    lapse = 1/(a*e*c)
    assert s.simplify(H.subs(gauge)) == 0
    qdot = [s.simplify(lapse*s.diff(H, mom).subs(gauge)) for mom in [PT, P, PL, pi]]
    pdot = [s.simplify(-lapse*s.diff(H, field).subs(gauge)) for field in [T, Q, L, phi]]
    expected_q = [1, P/c, -s.diff(reduced, c), s.diff(reduced, pi)]
    expected_p = [-s.diff(reduced, T), 0, -s.diff(reduced, L), -s.diff(reduced, phi)]
    assert all(s.simplify(x-y) == 0 for x, y in zip(qdot+pdot, expected_q+expected_p))
    assert s.simplify(-pdot[2]-W/c) == 0
    print('All eight homogeneous unreduced Hamilton equations match the revised reduction.', flush=True)
    return dict(reduced_H=str(reduced), all_eight_Hamilton_equations=True,
                c_equation='dc/dT=exp(2T+L)*V/(a*c)',
                constant_c_requires_zero_V=True,
                scope='Homogeneous exact canonical comparison; spatial constraint identities are separate.')


def spatial_reduction():
    """Check the revised reduction against all eight unreduced PDE components."""
    T, Q, L, phi = q = s.symbols('T Q L phi', real=True)
    Tx, Qx, Lx, phix = dq = s.symbols('Tx Qx Lx phix', real=True)
    Txx, Qxx, Lxx, phixx = ddq = s.symbols('Txx Qxx Lxx phixx', real=True)
    dddq = s.symbols('Txxx Qxxx Lxxx phixxx', real=True)
    PT, P, PL, pi = p = s.symbols('PT P PL pi', real=True)
    PTx, Px, PLx, pix = dp = s.symbols('PTx Px PLx pix', real=True)
    N, Nx, Nxx = s.symbols('N Nx Nxx', real=True)
    a, b, kap, gam, c = s.symbols('a b kap gam c', positive=True)
    cx, cxx, mass2, quartic, vacuum = s.symbols('cx cxx mass2 quartic vacuum', real=True)
    jets = dict(zip(q+dq+ddq+p+(N, Nx), dq+ddq+dddq+dp+(Nx, Nxx)))

    def D(expr):
        return sum(s.diff(expr, var)*velocity for var, velocity in jets.items())

    def euler(expr, i):
        return s.diff(expr, q[i])-D(s.diff(expr, dq[i]))+D(D(s.diff(expr, ddq[i])))

    e, f, vol = s.exp(-T-L/2), s.exp(T-L/2), s.exp(T+L/2)
    V = mass2*phi**2/2+quartic*phi**4/4+vacuum
    H = a*e*(P**2/2+PL**2/2-PT*PL)+b*f*(2*Txx+3*Tx**2/2+Qx**2/2-Lx*Tx)
    H += kap*e*pi**2/2+gam*f*phix**2/2+vol*V
    E = P**2+(b/a)*s.exp(2*T)*Qx**2+(kap/a)*pi**2+(gam/a)*s.exp(2*T)*phix**2
    W = s.exp(2*T+L)*V/a
    reduced = c/2+(E+2*W)/(2*c)
    lapse = 1/(a*e*c)
    source = (P*Qx+pi*phix+2*cx)/c
    source_x = (Px*Qx+P*Qxx+pix*phix+pi*phixx+2*cxx)/c-source*cx/c
    gauge = {Tx:0, Txx:0, PL:-c, PLx:-cx, PT:-reduced,
             N:lapse, Nx:lapse*(Lx/2-cx/c),
             Nxx:lapse*((Lx/2-cx/c)**2+Lxx/2-cxx/c+cx**2/c**2)}

    def restrict(expr):
        return s.simplify(expr.subs(gauge, simultaneous=True).subs({Lx:source, Lxx:source_x}))

    qdot = [restrict(s.diff(N*H, mom)) for mom in p]
    pdot = [restrict(-euler(N*H, i)) for i in range(4)]
    Qdot = P/c
    Ldot = -s.diff(reduced, c)
    cdot = W/c
    phidot = kap*pi/(a*c)
    Pdot = (b/a)*s.exp(2*T)*(Qxx/c-Qx*cx/c**2)
    pidot = (gam/a)*s.exp(2*T)*(phixx/c-phix*cx/c**2)-s.exp(2*T+L)*s.diff(V, phi)/(a*c)
    Qxdot = Px/c-P*cx/c**2
    phixdot = (kap/a)*(pix/c-pi*cx/c**2)
    Hdot = s.diff(reduced, T)+sum(s.diff(reduced, var)*rate for var, rate in
        [(L,Ldot),(c,cdot),(P,Pdot),(Qx,Qxdot),(phi,phidot),(phix,phixdot),(pi,pidot)])
    targets = [1, Qdot, Ldot, phidot, -Hdot, Pdot, -cdot, pidot]
    unmatched_PT_residual = s.factor(s.simplify(pdot[0]+Hdot))
    for index, (actual, expected) in enumerate(zip(qdot+pdot, targets)):
        # The eliminated equation is consistent only with the common
        # metric condition already selected by the normal bracket.
        assert s.simplify((actual-expected).subs(gam, a*b/kap)) == 0, index
    assert restrict(H) == 0
    print('All eight inhomogeneous unreduced Hamilton equations match the revised reduction.', flush=True)
    return dict(all_eight_Hamilton_PDE_components=True,
                common_cone_imposed='gamma=a*b/kappa',
                unmatched_PT_residual=str(unmatched_PT_residual),
                scalar_constraint=True, spatial_constraint='Lx=(P*Qx+pi*phix+2*cx)/c',
                scope='Exact symbolic jet identity on the gauge and both constraints; no PDE existence theorem.')


def evolving_clock():
    mass2, quartic = 0.5, 0.1

    def energy(t, y):
        Q, P, L, c, phi, pi, PT = y
        V = mass2*phi**2/2+quartic*phi**4/4
        W = np.exp(2*t+L)*V
        return c/2+(P*P+pi*pi+2*W)/(2*c)

    def rhs(t, y):
        Q, P, L, c, phi, pi, PT = y
        vol = np.exp(2*t+L)
        V = mass2*phi**2/2+quartic*phi**4/4
        W = vol*V
        return [P/c, 0, -0.5+(P*P+pi*pi+2*W)/(2*c*c), W/c,
                pi/c, -vol*(mass2*phi+quartic*phi**3)/c, -2*W/c]

    y0 = np.array([0.1, 0.2, 0., 1., 0.3, 0.1, 0.])
    y0[-1] = -energy(0., y0)
    times = np.linspace(0, 2, 401)
    sol = solve_ivp(rhs, (0, 2), y0, t_eval=times, rtol=2e-11, atol=2e-13)
    assert sol.success
    c = sol.y[3]
    assert np.min(np.diff(c)) >= -1e-12 and np.min(c) >= 1-1e-12
    shell_error = max(abs(y[-1]+energy(t, y)) for t, y in zip(times, sol.y.T))
    assert shell_error < 2e-9
    initial_force = rhs(0., y0)[3]
    assert initial_force > 0
    print(f'Dynamic clock: c(0)=1, c(2)={c[-1]:.9g}, shell residual={shell_error:.3g}', flush=True)
    return dict(initial_c=1., final_c=float(c[-1]), initial_c_force=float(initial_force),
                minimum_c=float(min(c)), maximum_constraint_shell_residual=float(shell_error),
                sample_count=len(times), mass_squared=mass2, quartic=quartic,
                final_scalar=float(sol.y[4, -1]),
                scope='Floating-point homogeneous classical ODE diagnostic; no existence or quantum claim.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_constraint_algebra=constraint_algebra(),
                  exact_homogeneous_reduction=homogeneous_reduction(),
                  exact_spatial_reduction=spatial_reduction(),
                  classical_clock_evolution=evolving_clock())
    sources = ['scripts/matter_clock_revision_audit.py',
               'UnifiedTheory/Audit/KFCausalMatterConstraintAlgebra.lean',
               'UnifiedTheory/Audit/KFCausalMatterArealReduction.lean',
               'UnifiedTheory/Audit/KFCausalTwoModeObstruction.lean']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A revised classical diagonal one-coordinate gravity/scalar target. '
                       'The spin dynamics, full three-dimensional closure, quantum anomaly control, '
                       'continuum limit and Standard Model are not derived by these checks.')
    target = root/'data/matter_clock_revision_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, flush=True)


if __name__ == '__main__':
    main()
