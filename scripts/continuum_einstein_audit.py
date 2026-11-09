#!/usr/bin/env python3
"""Free overlap continuum and an explicit classical metric-action benchmark.

The metric action is a new input, not selected by the causal growth law.
Finite scans check the analytic consistency proof, not quantum GR emergence.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import sympy as sym

from overlap_chirality_audit import GAMMA, GAMMA5
from compact_measure_holonomy_audit import FlatFamily

GAMMAS = np.array(GAMMA, complex)
G5 = np.array(GAMMA5, complex)


def overlap_symbol(spacing, momentum):
    k = spacing*np.asarray(momentum)
    w = np.sum(1-np.cos(k))-1
    r = np.sqrt(w*w+np.sum(np.sin(k)**2))
    return (np.eye(4)+(w*np.eye(4)+1j*np.einsum('a,aij->ij', np.sin(k), GAMMAS))/r)/spacing


def overlap_checks():
    family = FlatFamily((3,)*4)
    theta = np.array([.37, -.29, .43, .61])
    kernels, projectors, _, _ = family.blocks(theta, 1)
    block_error = 0.
    for k, h in zip(family.momenta-theta/3, kernels):
        radius = np.linalg.norm(np.linalg.eigvalsh(h), ord=np.inf)
        block_error = max(block_error, float(np.linalg.norm(overlap_symbol(1, k)-(np.eye(4)+G5@h/radius))))
    assert block_error < 1e-13
    mass = .7
    momenta = np.pi*np.array([[2, 0, 2, 1], [2, -2, 0, 3], [0, 0, 0, 1]])
    rows = []
    for length in [16, 32, 64, 128, 256]:
        spacing = 1/length
        errors, ratios, resolvents, chiral = [], [], [], []
        for p in momenta:
            normp = np.linalg.norm(p)
            assert spacing*normp <= 1
            discrete = overlap_symbol(spacing, p)
            continuum = 1j*np.einsum('a,aij->ij', p, GAMMAS)
            error = np.linalg.norm(discrete-continuum, ord=2)
            bound = spacing*normp**2
            inverse_error = np.linalg.norm(np.linalg.inv(discrete+mass*np.eye(4))
                                           - np.linalg.inv(continuum+mass*np.eye(4)), ord=2)
            # P_a-P_left = gamma5*(a D_a)/2, from the actual projector.
            chiral_error = np.linalg.norm(G5@(spacing*discrete)/2, ord=2)
            assert error <= bound and inverse_error <= bound/mass**2
            assert chiral_error <= spacing*normp
            errors.append(float(error)); ratios.append(float(error/bound))
            resolvents.append(float(inverse_error)); chiral.append(float(chiral_error))
        rows.append(dict(length=length, maximum_operator_error=max(errors),
                         maximum_error_over_bound=max(ratios),
                         maximum_resolvent_error=max(resolvents),
                         maximum_chiral_projector_error=max(chiral)))
    assert rows[-1]['maximum_operator_error'] < rows[0]['maximum_operator_error']/12
    return dict(existing_flat_block_error=block_error, positive_resolvent_mass=mass, rows=rows,
                scope='Free Euclidean operator on supplied flat geometry; interacting QFT remains open')


def connection(inv, dg):
    # dg[n, derivative, metric_row, metric_column].
    lower = dg.transpose(0, 2, 1, 3)+dg.transpose(0, 2, 3, 1)-dg
    return .5*np.einsum('nar,nrbc->nabc', inv, lower)


def gamma_quadratic(inv, left, right):
    return (np.einsum('nuv,nrus,nsvr->n', inv, left, right)
            - np.einsum('nuv,nruv,nsrs->n', inv, left, right))


def geometry(g, dg, ddg=None):
    inv = np.linalg.inv(g)
    determinants = np.linalg.det(g)
    assert np.all(determinants < 0)
    volume = np.sqrt(-determinants)
    gamma = connection(inv, dg)
    result = dict(inv=inv, volume=volume, gamma=gamma,
                  quadratic=gamma_quadratic(inv, gamma, gamma))
    if ddg is not None:
        dinv = -np.einsum('nai,ndij,njb->ndab', inv, dg, inv)
        dgamma = np.stack([connection(dinv[:, d], dg)+connection(inv, ddg[:, d])
                          for d in range(4)], axis=1)
        ricci = (np.einsum('nrrvu->nuv', dgamma)-np.einsum('nvrru->nuv', dgamma)
                 + np.einsum('nrrs,nsvu->nuv', gamma, gamma)
                 - np.einsum('nrvs,nsru->nuv', gamma, gamma))
        scalar = np.einsum('nuv,nuv->n', inv, ricci)
        einstein = ricci-scalar[:, None, None]*g/2
        # Independent divergence term in sqrt(-g) R = sqrt(-g) Q + div V.
        def boundary_vector(inverse, christoffel):
            return np.einsum('nuv,nruv->nr', inverse, christoffel)-np.einsum('nru,nsus->nr', inverse, christoffel)
        vector = boundary_vector(inv, gamma)
        dvector = np.stack([boundary_vector(dinv[:, d], gamma)
                            + boundary_vector(inv, dgamma[:, d]) for d in range(4)], axis=1)
        log_volume_derivative = .5*np.einsum('nab,ndba->nd', inv, dg)
        divergence = volume*(np.einsum('nd,nd->n', log_volume_derivative, vector)
                             + np.einsum('nrr->n', dvector))
        result.update(ricci=ricci, scalar=scalar, einstein=einstein, boundary_divergence=divergence)
    return result


def lagrangian(g, dg, phi, dphi, kappa=1., cosmological=0., mass_squared=0., quartic=0.):
    z = geometry(g, dg)
    potential = mass_squared*phi**2+quartic*phi**4/2  # twice the scalar potential
    kinetic = np.einsum('nab,na,nb->n', z['inv'], dphi, dphi)+potential
    return z['volume']*((z['quadratic']-2*cosmological)/(2*kappa)-kinetic/2)


def first_variation(g, dg, phi, dphi, h, dh, psi, dpsi,
                    kappa=1., cosmological=0., mass_squared=0., quartic=0.):
    z = geometry(g, dg)
    inv, volume, gamma = z['inv'], z['volume'], z['gamma']
    di = -inv@h@inv
    dv = volume*np.einsum('nab,nba->n', inv, h)/2
    dc = connection(di, dg)+connection(inv, dh)
    dq = (gamma_quadratic(di, gamma, gamma)+gamma_quadratic(inv, dc, gamma)
          + gamma_quadratic(inv, gamma, dc))
    kinetic = np.einsum('nab,na,nb->n', inv, dphi, dphi)+mass_squared*phi**2+quartic*phi**4/2
    dk = (np.einsum('nab,na,nb->n', di, dphi, dphi)
          + 2*np.einsum('nab,na,nb->n', inv, dphi, dpsi)
          + 2*(mass_squared*phi+quartic*phi**3)*psi)
    return (dv*(z['quadratic']-2*cosmological)+volume*dq)/(2*kappa)-(dv*kinetic+volume*dk)/2


def einstein_variation(g, dg, ddg, phi, dphi, ddphi, h, psi,
                       kappa=1., cosmological=0., mass_squared=0., quartic=0.):
    z = geometry(g, dg, ddg)
    inv = z['inv']
    kinetic = np.einsum('nab,na,nb->n', inv, dphi, dphi)+mass_squared*phi**2+quartic*phi**4/2
    stress = np.einsum('na,nb->nab', dphi, dphi)-g*kinetic[:, None, None]/2
    residual = z['einstein']+cosmological*g-kappa*stress
    kg = (np.einsum('nab,nab->n', inv, ddphi)
          - np.einsum('nab,nrab,nr->n', inv, z['gamma'], dphi)
          - mass_squared*phi-quartic*phi**3)
    response = z['volume']*(-np.einsum('nab,nab->n', inv@residual@inv, h)/(2*kappa)+kg*psi)
    return response, residual, kg


def homogeneous_fields(kind):
    """Nontrivial tensor benchmark; one coordinate varies, with unit spatial volume."""
    t = sym.symbols('t', real=True)
    if kind == 'general':
        frame = sym.eye(4)
        frame[0, 1] = sym.sin(2*sym.pi*t)/12
        frame[1, 2] = sym.cos(2*sym.pi*t)/14
        frame[2, 3] = sym.sin(4*sym.pi*t)/16
        frame[3, 0] = sym.cos(2*sym.pi*t)/20
        scales = [-sym.exp(sym.sin(2*sym.pi*t)/5), sym.exp(sym.cos(2*sym.pi*t)/6),
                  sym.exp(sym.sin(4*sym.pi*t)/7), sym.exp(sym.cos(4*sym.pi*t)/8)]
        metric = frame.T*sym.diag(*scales)*frame
        scalar = sym.sin(2*sym.pi*t)/14+sym.cos(4*sym.pi*t)/30
        parameters = dict(kappa=.8, cosmological=.11, mass_squared=.7, quartic=.3)
    elif kind == 'de_sitter':
        metric = sym.diag(-1, 1, 1, 1)/(t-2)**2
        scalar = sym.Integer(0)
        parameters = dict(kappa=1., cosmological=3.)
    elif kind == 'scalar_flrw':
        metric = sym.diag(-1, (1+t)**sym.Rational(2, 3), (1+t)**sym.Rational(2, 3), (1+t)**sym.Rational(2, 3))
        scalar = sym.sqrt(sym.Rational(2, 3))*sym.log(1+t)
        parameters = dict(kappa=1.)
    else:
        raise ValueError(kind)
    expressions = [list(metric), list(metric.diff(t)), list(metric.diff(t, 2)),
                   [scalar, sym.diff(scalar, t), sym.diff(scalar, t, 2)]]
    functions = [sym.lambdify(t, row, modules='numpy', cse=True) for row in expressions]

    def evaluate(points):
        points = np.asarray(points)
        values = [np.stack([np.broadcast_to(value, points.shape) for value in function(points)], axis=-1)
                  for function in functions]
        n = len(points)
        g = values[0].reshape(n, 4, 4)
        dg, ddg = np.zeros((n, 4, 4, 4)), np.zeros((n, 4, 4, 4, 4))
        dg[:, 0] = values[1].reshape(n, 4, 4)
        ddg[:, 0, 0] = values[2].reshape(n, 4, 4)
        phi = values[3][:, 0]
        dphi, ddphi = np.zeros((n, 4)), np.zeros((n, 4, 4))
        dphi[:, 0] = values[3][:, 1]
        ddphi[:, 0, 0] = values[3][:, 2]
        return g, dg, ddg, phi, dphi, ddphi
    return evaluate, parameters


def bump(points):
    points = np.asarray(points)
    inside = (points >= 0) & (points <= 1)
    value = np.where(inside, 256*points**4*(1-points)**4, 0.)
    derivative = np.where(inside, 1024*points**3*(1-points)**3*(1-2*points), 0.)
    return value, derivative


def direction(points, component):
    n = len(points)
    b, db = bump(points)
    h, dh, psi, dpsi = np.zeros((n, 4, 4)), np.zeros((n, 4, 4, 4)), np.zeros(n), np.zeros((n, 4))
    pairs = [(i, j) for i in range(4) for j in range(i, 4)]
    if component < 10:
        i, j = pairs[component]
        h[:, i, j] = h[:, j, i] = b
        dh[:, 0, i, j] = dh[:, 0, j, i] = db
    else:
        psi = b
        dpsi[:, 0] = db
    return h, dh, psi, dpsi


def continuum_checks(kind):
    fields, parameters = homogeneous_fields(kind)
    nodes, weights = np.polynomial.legendre.leggauss(200)
    points, weights = (nodes+1)/2, weights/2
    g, dg, ddg, phi, dphi, ddphi = fields(points)
    z = geometry(g, dg, ddg)
    boundary_error = float(np.max(abs(z['volume']*(z['scalar']-z['quadratic'])-z['boundary_divergence'])))
    assert boundary_error < 1e-10
    references = []
    continuum_identity_error = 0.
    for component in range(11):
        h, dh, psi, dpsi = direction(points, component)
        by_action = weights@first_variation(g, dg, phi, dphi, h, dh, psi, dpsi, **parameters)
        response, einstein, kg = einstein_variation(g, dg, ddg, phi, dphi, ddphi, h, psi, **parameters)
        by_equation = weights@response
        continuum_identity_error = max(continuum_identity_error, abs(by_action-by_equation))
        references.append(float(by_equation))
    assert continuum_identity_error < 1e-10
    if kind != 'general':
        assert np.max(abs(einstein)) < 1e-11 and np.max(abs(kg)) < 1e-11
    continuum_action = float(weights@lagrangian(g, dg, phi, dphi, **parameters))
    rows = []
    finite_variation_error = None
    for length in [16, 32, 64, 128, 256]:
        spacing = 1/length
        x = (np.arange(length)+.5)*spacing
        g, dg, _, phi, dphi, _ = fields(x)
        plus, minus = fields(x+spacing), fields(x-spacing)
        dg_plus, dg_minus = np.zeros_like(dg), np.zeros_like(dg)
        dphi_plus, dphi_minus = np.zeros_like(dphi), np.zeros_like(dphi)
        dg_plus[:, 0], dg_minus[:, 0] = (plus[0]-g)/spacing, (g-minus[0])/spacing
        dphi_plus[:, 0], dphi_minus[:, 0] = (plus[3]-phi)/spacing, (phi-minus[3])/spacing
        variations = []
        for component in range(11):
            h, dh, psi, dpsi = direction(x, component)
            dp, dm = direction(x+spacing, component), direction(x-spacing, component)
            dh_plus, dh_minus = np.zeros_like(dh), np.zeros_like(dh)
            dpsi_plus, dpsi_minus = np.zeros_like(dpsi), np.zeros_like(dpsi)
            dh_plus[:, 0], dh_minus[:, 0] = (dp[0]-h)/spacing, (h-dm[0])/spacing
            dpsi_plus[:, 0], dpsi_minus[:, 0] = (dp[2]-psi)/spacing, (psi-dm[2])/spacing
            variations.append(float(.5*np.mean(
                first_variation(g, dg_plus, phi, dphi_plus, h, dh_plus, psi, dpsi_plus, **parameters)
                + first_variation(g, dg_minus, phi, dphi_minus, h, dh_minus, psi, dpsi_minus, **parameters))))
            if kind == 'general' and length == 64 and component == 3:
                delta = 1e-5
                def varied_action(sign):
                    return .5*np.mean(
                        lagrangian(g+sign*delta*h, dg_plus+sign*delta*dh_plus,
                                   phi+sign*delta*psi, dphi_plus+sign*delta*dpsi_plus, **parameters)
                        + lagrangian(g+sign*delta*h, dg_minus+sign*delta*dh_minus,
                                     phi+sign*delta*psi, dphi_minus+sign*delta*dpsi_minus, **parameters))
                plus_action, minus_action = varied_action(1), varied_action(-1)
                finite_variation_error = abs((plus_action-minus_action)/(2*delta)-variations[-1])
                assert finite_variation_error < 1e-8
        error = float(np.max(abs(np.array(variations)-references)))
        lattice_action = .5*np.mean(lagrangian(g, dg_plus, phi, dphi_plus, **parameters)
                                    + lagrangian(g, dg_minus, phi, dphi_minus, **parameters))
        rows.append(dict(length=length, action_error=abs(float(lattice_action)-continuum_action),
                         maximum_first_variation_error=error, first_variations=variations))
    assert rows[-1]['maximum_first_variation_error'] < rows[0]['maximum_first_variation_error']/150
    rate = rows[-2]['maximum_first_variation_error']/rows[-1]['maximum_first_variation_error']
    assert 3.5 < rate < 4.5
    print(kind, 'first-variation refinement ratio', rate, flush=True)
    return dict(case=kind, boundary_identity_error=boundary_error,
                integrated_einstein_variation_error=float(continuum_identity_error),
                exact_solution_einstein_residual=float(np.max(abs(einstein))) if kind != 'general' else None,
                exact_solution_scalar_residual=float(np.max(abs(kg))) if kind != 'general' else None,
                independent_action_difference_error=finite_variation_error,
                continuum_first_variations=references, rows=rows, final_refinement_ratio=rate)


def random_jet_checks():
    rng = np.random.default_rng(2026091014)
    n = 24
    frame = np.eye(4)+rng.normal(0, .08, (n, 4, 4))
    g = frame.transpose(0, 2, 1)@np.diag([-1., 1., 1., 1.])@frame
    dg = rng.normal(0, .1, (n, 4, 4, 4))
    dg = (dg+dg.swapaxes(-1, -2))/2
    ddg = rng.normal(0, .1, (n, 4, 4, 4, 4))
    ddg = (ddg+ddg.swapaxes(-1, -2))/2
    ddg = (ddg+ddg.swapaxes(1, 2))/2
    z = geometry(g, dg, ddg)
    error = float(np.max(abs(z['volume']*(z['scalar']-z['quadratic'])-z['boundary_divergence'])))
    symmetry = float(np.max(abs(z['ricci']-z['ricci'].swapaxes(-1, -2))))
    assert error < 1e-12 and symmetry < 1e-12
    return dict(generic_four_coordinate_jets=n, boundary_identity_error=error, ricci_symmetry_error=symmetry)


def checkerboard_checks():
    length = 16
    spacing = 1/length
    alternating = (-1.)**np.arange(length)
    scale = 1+.05*alternating
    g = scale[:, None, None]*np.diag([-1., 1., 1., 1.])
    central = np.zeros((length, 4, 4, 4))
    plus, minus = central.copy(), central.copy()
    plus[:, 1] = (np.roll(g, -1, axis=0)-g)/spacing
    minus[:, 1] = (g-np.roll(g, 1, axis=0))/spacing
    zero, zero_gradient = np.zeros(length), np.zeros((length, 4))
    central_action = float(np.mean(lagrangian(g, central, zero, zero_gradient)))
    central_variation = float(np.mean(first_variation(
        g, central, zero, zero_gradient, np.ones_like(g), np.ones_like(central), zero, zero_gradient)))
    improved_action = float(.5*np.mean(lagrangian(g, plus, zero, zero_gradient)
                                      + lagrangian(g, minus, zero, zero_gradient)))
    h = alternating[:, None, None]*np.diag([-1., 1., 1., 1.])
    dh_plus, dh_minus = np.zeros_like(plus), np.zeros_like(minus)
    dh_plus[:, 1] = (np.roll(h, -1, axis=0)-h)/spacing
    dh_minus[:, 1] = (h-np.roll(h, 1, axis=0))/spacing
    improved_variation = float(.5*np.mean(
        first_variation(g, plus, zero, zero_gradient, h, dh_plus, zero, zero_gradient)
        + first_variation(g, minus, zero, zero_gradient, h, dh_minus, zero, zero_gradient)))
    expected_variation = 6*.05/(spacing**2*(1-.05**2)**2)
    assert abs(improved_variation-expected_variation) < 1e-10
    assert central_action == 0 and central_variation == 0 and improved_action > 0 and improved_variation > 0
    # All Fourier modes of a massless spatial scalar: the averaged one-sided
    # kinetic form has only the constant zero, unlike the centered stencil.
    momenta = 2*np.pi*np.arange(length)/length
    centered_eigenvalues = np.sin(momenta)**2/spacing**2
    improved_eigenvalues = 4*np.sin(momenta/2)**2/spacing**2
    centered_zeros = np.flatnonzero(centered_eigenvalues < 1e-20).tolist()
    improved_zeros = np.flatnonzero(improved_eigenvalues < 1e-20).tolist()
    assert centered_zeros == [0, length//2] and improved_zeros == [0]
    return dict(length=length, old_metric_action=central_action, old_metric_variation=central_variation,
                new_metric_action=improved_action, new_metric_variation=improved_variation,
                centered_scalar_zero_modes=centered_zeros,
                new_scalar_zero_modes=improved_zeros,
                scope='This exact checkerboard defect is removed; full gravitational stability is not proved')


def write_report(result):
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/continuum_einstein_audit.py', 'scripts/overlap_chirality_audit.py',
               'scripts/compact_measure_holonomy_audit.py', 'scripts/radial_measure_audit.py',
               'CONTINUUM_EINSTEIN_BRIDGE.md', 'UnifiedTheory/Audit/KFCausalContinuumEinstein.lean']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    result['scope'] = 'Free flat overlap continuum plus a chosen classical metric-scalar action; smooth-limit existence and microscopic selection unproved'
    output = root/'data/continuum_einstein_audit.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print('Wrote', output, flush=True)


def main():
    write_report(dict(overlap=overlap_checks(), random_jets=random_jet_checks(), checkerboard=checkerboard_checks(),
                      gravity=[continuum_checks(kind) for kind in ['general', 'de_sitter', 'scalar_flrw']]))


if __name__ == '__main__':
    main()
