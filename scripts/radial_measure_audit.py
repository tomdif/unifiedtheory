#!/usr/bin/env python3
"""Radial projector current, exact Ward defect, and a closing-Dirac-gap test.

This is the curvature part of measure reconstruction. A gauge-invariant
local anomaly primitive is still missing. Float64 is not a proof certificate.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import sympy as s

from overlap_chirality_audit import GAMMA, GAMMA5, equal
from gauge_dressed_measure_audit import DressedOverlap, SPECIES
from positive_measure_audit import positive_current
from chiral_measure_audit import determinant_transport


class RectangularOverlap:
    """Same Wilson/overlap conventions; arbitrary lengths and either time boundary."""
    def __init__(self, lengths, antiperiodic=True):
        self.lengths = tuple(lengths)
        sites = list(itertools.product(*(range(n) for n in lengths)))
        self.n = len(sites)
        idx = {x: j for j, x in enumerate(sites)}
        previous = [np.array([idx[tuple((v-1) % lengths[k] if k == mu else v
                                       for k, v in enumerate(x))] for x in sites]) for mu in range(4)]
        eye = np.eye(4*self.n, dtype=complex)
        g5 = np.kron(np.array(GAMMA5, complex), np.eye(self.n))
        plus = [(np.eye(4)+np.array(g, complex))/2 for g in GAMMA]
        self.geom = SimpleNamespace(sites=sites, previous=previous, eye=eye, g5=g5,
                                    plus=plus, minus=[np.eye(4)-p for p in plus])
        self.eye = eye
        self.pbar = (eye+g5)/2
        self.boundary = np.ones((4, self.n))
        if antiperiodic:
            self.boundary[3] = [-1 if x[3] == 0 else 1 for x in sites]

    def kernel(self, links, charge, first=None, second=None):
        h = 3*self.eye.copy() if first is None else np.zeros_like(self.eye)
        for mu in range(4):
            values = self.boundary[mu]*links[mu]**charge
            if first is not None:
                values = values*(1j*charge*first[mu])
            if second is not None:
                values = values*(1j*charge*second[mu])
            shift = np.zeros((self.n, self.n), complex)
            shift[np.arange(self.n), self.geom.previous[mu]] = values
            h -= np.kron(self.geom.plus[mu], shift)+np.kron(self.geom.minus[mu], shift.conj().T)
        return self.geom.g5@h

    def operator(self, links, charge):
        h = self.kernel(links, charge)
        assert np.linalg.norm(h-h.conj().T) < 1e-11
        values, vectors = np.linalg.eigh(h)
        positive = values > 0
        frame = vectors[:, positive]
        p = frame@frame.conj().T
        d = self.eye+self.geom.g5@(2*p-self.eye)
        mask = positive[:, None] != positive[None, :]
        numerator = positive.astype(float)[:, None]-positive.astype(float)[None, :]
        denominator = values[:, None]-values[None, :]
        divided = np.zeros_like(denominator)
        divided[mask] = numerator[mask]/denominator[mask]
        return dict(p=p, d=d, v=frame, values=values, vectors=vectors, positive=positive,
                    mask=mask, divided=divided, gap=float(np.min(np.abs(values))))

    def spectral_derivative(self, spectrum, dh):
        v = spectrum['vectors']
        return v@(spectrum['divided']*(v.conj().T@dh@v))@v.conj().T

    def projector_derivative(self, links, charge, spectrum, direction):
        return self.spectral_derivative(spectrum, self.kernel(links, charge, direction))

    def projector_jet(self, links, charge, spectrum, first, second):
        """First and mixed second derivatives, including repeated-eigenvalue blocks.

        Off-sign blocks follow from differentiating [H,P]=0 twice;
        same-sign blocks follow from differentiating P^2=P twice.
        Only opposite-sign eigenvalues are divided, hence the Wilson gap
        alone protects this calculation, even if D has zero modes.
        """
        v = spectrum['vectors']
        ha = v.conj().T@self.kernel(links, charge, first)@v
        hb = v.conj().T@self.kernel(links, charge, second)@v
        hab = v.conj().T@self.kernel(links, charge, first, second)@v
        a = spectrum['divided']*ha
        b = spectrum['divided']*hb
        positive = spectrum['positive']
        bits = positive.astype(float)
        rhs = -(ha@b-b@ha+hb@a-a@hb+hab*(bits[None, :]-bits[:, None]))
        values = spectrum['values']
        denominator = values[:, None]-values[None, :]
        mask = spectrum['mask']
        ab = np.zeros_like(rhs)
        ab[mask] = rhs[mask]/denominator[mask]
        products = a@b+b@a
        pp = positive[:, None] & positive[None, :]
        nn = (~positive[:, None]) & (~positive[None, :])
        ab[pp] = -products[pp]
        ab[nn] = products[nn]
        return v@a@v.conj().T, v@b@v.conj().T, v@ab@v.conj().T


def density(model, p, charge):
    return charge*np.diag(p-model.pbar).real.reshape(4, model.n).sum(axis=0)


def curvature(p, a, b):
    return float((1j*np.trace(p@(a@b-b@a))).real)


def radial_current(model, theta, charge, direction, count=8, response=None):
    nodes, weights = np.polynomial.legendre.leggauss(count)
    answer = 0.
    derivative = 0.
    averaged_density = np.zeros(model.n)
    minimum_gap = np.inf
    for t, weight in zip((nodes+1)/2, weights/2):
        links = np.exp(1j*t*theta)
        sp = model.operator(links, charge)
        if response is None:
            pa = model.projector_derivative(links, charge, sp, theta)
            pe = model.projector_derivative(links, charge, sp, direction)
        else:
            pa, pf, paf = model.projector_jet(links, charge, sp, theta, response)
            pe, _, pef = model.projector_jet(links, charge, sp, direction, response)
            # The omitted third-tangent trace is exactly zero (Lean theorem).
            derivative += weight*(t*curvature(sp['p'], pf+t*paf, pe)+
                                  t*t*curvature(sp['p'], pa, pef))
        answer += weight*t*curvature(sp['p'], pa, pe)
        averaged_density += weight*density(model, sp['p'], charge)
        minimum_gap = min(minimum_gap, sp['gap'])
    return dict(current=float(answer), response=float(derivative),
                averaged_density=averaged_density, minimum_kernel_gap=minimum_gap)


def positive_response(model, theta, charge, probe, remote):
    links = np.exp(1j*theta)
    sp = model.operator(links, charge)
    pe, pf, pef = model.projector_jet(links, charge, sp, probe, remote)
    de, df, def_ = [2*model.geom.g5@a for a in [pe, pf, pef]]
    re, rf, ref = [np.linalg.solve(sp['d'], a) for a in [de, df, def_]]
    response = np.trace(-rf@re@sp['p']+ref@sp['p']+re@pf).imag
    return float(response), sp


def base_field(model, amplitude=.018):
    base = np.random.default_rng(2026090902).uniform(-amplitude, amplitude, (4, 16))
    lookup = {x: j for j, x in enumerate(itertools.product(range(2), repeat=4))}
    return np.array([base[:, lookup[tuple(v % 2 for v in x)]] for x in model.geom.sites]).T


def exact_checks():
    cc = GAMMA[1]*GAMMA[3]
    equal(cc*cc.H, s.eye(4))
    equal(cc*cc.conjugate(), -s.eye(4))
    for g in GAMMA+[GAMMA5]:
        equal(cc*g.conjugate()*cc.H, g)
    moments = {str(k): sum(m*q**k for _, q, m in SPECIES) for k in [1, 3, 5, 7]}
    assert moments == {'1': 0, '3': 0, '5': 4320, '7': 226800}
    assert sum(m*abs(q)**5 for _, q, m in SPECIES) == 11436
    p = s.diag(1, 0)
    a, b, c = s.Matrix([[0, 1], [1, 0]]), s.Matrix([[0, s.I], [-s.I, 0]]), s.Matrix([[0, 2+s.I], [2-s.I, 0]])
    assert (a*b*c).trace() == 0
    k = a*p-p*a
    flux = s.Matrix(2, 2, lambda x, y: k[x, y]*p[y, x]-p[x, y]*k[y, x])
    assert flux+flux.T == s.zeros(2)
    # A non-diagonal projector makes the divergence transgression nontrivial.
    v = s.Matrix([3, 4])/5
    p = v*v.H
    generator = s.Matrix([[0, 1], [-1, 0]])
    a = generator*p-p*generator
    k = a*p-p*a
    flux = s.Matrix(2, 2, lambda x, y: k[x, y]*p[y, x]-p[x, y]*k[y, x])
    assert [sum(flux[x, y] for y in range(2)) for x in range(2)] == list(a.diagonal())
    assert any(value != 0 for value in flux)
    # The moving gauge generator adds a term to K; it does not transform covariantly.
    v = s.Matrix([1, 1, 1, 1])/2
    w = s.Matrix([1, s.I, 0, -1-s.I])/2
    p = v*v.H+w*w.H
    x = s.diag(s.I, 2*s.I, -s.I, 3*s.I)
    extra = (x*p-p*x)*p-p*(x*p-p*x)
    changed_flux = s.simplify(s.Matrix(4, 4, lambda i, j: extra[i, j]*p[j, i]-p[i, j]*extra[j, i]))
    assert changed_flux != s.zeros(4)
    assert all(sum(changed_flux[i, j] for j in range(4)) == 0 for i in range(4))
    return dict(arithmetic="exact SymPy complex rational matrices",
                charge_conjugation_matrix=str(cc), antiunitary_square="-I",
                hypercharge_moments=moments, absolute_fifth_moment=11436,
                tangent_triple_trace_zero=True, pair_flux_divergence=True,
                moving_gauge_flux_changes=True, moving_gauge_flux_divergence_zero=True)


def differential_checks():
    model = RectangularOverlap([2, 2, 2, 2])
    theta = base_field(model)
    links = np.exp(1j*theta)
    rng = np.random.default_rng(2026090903)
    u, v = [rng.uniform(-1, 1, theta.shape) for _ in range(2)]
    q = 6
    sp = model.operator(links, q)
    legacy = DressedOverlap().operator(links, q)
    assert np.linalg.norm(sp['p']-legacy['p']) < 1e-12
    assert np.linalg.norm(sp['d']-legacy['d']) < 1e-12
    pu, pv, puv = model.projector_jet(links, q, sp, u, v)
    projection_residual = float(np.linalg.norm(puv@sp['p']+sp['p']@puv+pu@pv+pv@pu-puv))
    assert projection_residual < 1e-10
    h = model.kernel(links, q)
    hu, hv, huv = model.kernel(links, q, u), model.kernel(links, q, v), model.kernel(links, q, u, v)
    comm_residual = float(np.linalg.norm(h@puv-puv@h+hu@pv-pv@hu+hv@pu-pu@hv+huv@sp['p']-sp['p']@huv))
    assert comm_residual < 1e-9
    jet_rows = []
    rad = radial_current(model, theta, q, u, response=v)
    pos, _ = positive_response(model, theta, q, u, v)
    for step in [2e-4, 1e-4, 5e-5]:
        lp, lm = np.exp(1j*(theta+step*v)), np.exp(1j*(theta-step*v))
        spp, spm = model.operator(lp, q), model.operator(lm, q)
        finite = (model.projector_derivative(lp, q, spp, u)-model.projector_derivative(lm, q, spm, u))/(2*step)
        rp = radial_current(model, theta+step*v, q, u)['current']
        rm = radial_current(model, theta-step*v, q, u)['current']
        pp, pm = positive_current(model, lp, q, u), positive_current(model, lm, q, u)
        jet_rows.append(dict(step=step, projector_hessian_error=float(np.linalg.norm(finite-puv)),
                             radial_response_error=abs((rp-rm)/(2*step)-rad['response']),
                             positive_response_error=abs((pp-pm)/(2*step)-pos)))
    assert jet_rows[-1]['projector_hessian_error'] < 1e-4
    assert jet_rows[-1]['projector_hessian_error'] < jet_rows[0]['projector_hessian_error']/12
    assert jet_rows[-1]['radial_response_error'] < 1e-7
    assert jet_rows[-1]['positive_response_error'] < 1e-7
    # Curl uses the full analytic Hessian response, independently of projector curvature.
    swapped = radial_current(model, theta, q, v, response=u)
    curl = swapped['response']-rad['response']
    target = curvature(sp['p'], pu, pv)
    assert abs(curl-target) < 1e-10
    # Free periodic D has exact zero modes; radial construction never inverts it.
    periodic = RectangularOverlap([2, 2, 2, 4], antiperiodic=False)
    free = periodic.operator(np.ones((4, periodic.n), complex), q)
    constant_spinors = np.kron(np.eye(4), np.ones((periodic.n, 1))/np.sqrt(periodic.n))
    zero_residual = float(np.linalg.norm(free['d']@constant_spinors))
    assert zero_residual < 1e-12 and free['gap'] > .99
    rd = radial_current(periodic, np.zeros((4, periodic.n)), q,
                        np.ones((4, periodic.n)))
    assert abs(rd['current']) < 1e-12
    return dict(operator_legacy_agreement=True, projector_hessian_identity_residual=projection_residual,
                kernel_commutator_hessian_residual=comm_residual, finite_difference_checks=jet_rows,
                radial_curl=curl, projector_curvature=target, curl_error=abs(curl-target),
                free_periodic_dirac_zero_residual=zero_residual, free_periodic_kernel_gap=free['gap'],
                radial_current_at_exact_dirac_zero=rd['current'])


def ward_and_scaling_checks():
    model = RectangularOverlap([2, 2, 2, 2])
    theta = base_field(model)
    rng = np.random.default_rng(2026090904)
    omega = rng.uniform(-1, 1, model.n)
    gauge_direction = np.array([omega-omega[prev] for prev in model.geom.previous])
    rows = []
    for scale in [1., .5, .25]:
        current, endpoint, average = 0., np.zeros(model.n), np.zeros(model.n)
        terms = []
        for name, q, multiplicity in SPECIES:
            sp = model.operator(np.exp(1j*scale*theta), q)
            radial = radial_current(model, scale*theta, q, gauge_direction)
            a = density(model, sp['p'], q)
            defect = radial['current']+float(a@omega)
            target = float(radial['averaged_density']@omega)
            assert abs(defect-target) < 1e-11
            terms.append(dict(species=name, charge=q, multiplicity=multiplicity,
                              ward_defect=defect, predicted_defect=target,
                              endpoint_density_norm=float(np.linalg.norm(a))))
            current += multiplicity*radial['current']
            endpoint += multiplicity*a
            average += multiplicity*radial['averaged_density']
        rows.append(dict(field_scale=scale, radial_gauge_current=current,
                         endpoint_anomaly_contraction=float(endpoint@omega),
                         integrated_defect=float(average@omega),
                         total_ward_defect=current+float(endpoint@omega),
                         endpoint_density_norm=float(np.linalg.norm(endpoint)),
                         averaged_density_norm=float(np.linalg.norm(average)), terms=terms))
    assert abs(rows[0]['integrated_defect']) > 1e-10
    ratios = [rows[j]['endpoint_density_norm']/rows[j+1]['endpoint_density_norm'] for j in range(2)]
    assert all(14 < ratio < 18 for ratio in ratios)
    # Charge conjugation explains even field dependence of the bare density.
    cc = np.kron(np.array(GAMMA[1]*GAMMA[3], complex), np.eye(model.n))
    sp = model.operator(np.exp(1j*theta), 6)
    flipped = model.operator(np.exp(-1j*theta), 6)
    conjugation_error = float(np.linalg.norm(flipped['p']-cc@sp['p'].conj()@cc.conj().T))
    assert conjugation_error < 1e-11
    return dict(random_seed=2026090904, rows=rows, density_halving_ratios=ratios,
                charge_conjugation_residual=conjugation_error,
                limitation="quartic suppression is not exact vanishing; a local gauge-invariant primitive is still required")


def closing_gap_scan():
    rows = []
    for time_length in [4, 8, 12, 16, 24]:
        model = RectangularOverlap([2, 2, 2, time_length])
        theta = base_field(model)
        idx = {x: j for j, x in enumerate(model.geom.sites)}
        probe, remote = np.zeros_like(theta), np.zeros_like(theta)
        probe[0, idx[(0, 0, 0, 0)]] = 1
        remote[1, idx[(0, 0, 0, time_length//2)]] = 1
        terms = []
        for name, q, multiplicity in SPECIES:
            positive, spectrum = positive_response(model, theta, q, probe, remote)
            radial = radial_current(model, theta, q, probe, count=4, response=remote)
            terms.append(dict(species=name, charge=q, multiplicity=multiplicity,
                              positive_response=positive, radial_response=radial['response'],
                              kernel_gap=spectrum['gap']))
            if q == 6:
                dirac_gap = float(np.linalg.svd(spectrum['d'], compute_uv=False)[-1])
        positive_sum = sum(term['multiplicity']*term['positive_response'] for term in terms)
        radial_sum = sum(term['multiplicity']*term['radial_response'] for term in terms)
        rows.append(dict(time_length=time_length, minimum_endpoint_distance=time_length//2,
                         positive_hypercharge_response=positive_sum, radial_hypercharge_response=radial_sum,
                         charge_six_dirac_gap=dirac_gap, terms=terms))
        print(f"T={time_length}: positive={positive_sum:.9g}, radial={radial_sum:.9g}", flush=True)
    # Check quadrature convergence for every species at the most separated pair.
    quadrature_rows = []
    for old in rows[-1]['terms']:
        refined = radial_current(model, theta, old['charge'], probe, count=8, response=remote)['response']
        error = abs(refined-old['radial_response'])
        assert error < 1e-12
        quadrature_rows.append(dict(charge=old['charge'], four_node_response=old['radial_response'],
                                    eight_node_response=refined, error=error))
    # Independently differentiate both currents at the largest volume for charge six.
    difference_rows = []
    for step in [1e-3, 5e-4]:
        rp = radial_current(model, theta+step*remote, 6, probe, count=8)['current']
        rm = radial_current(model, theta-step*remote, 6, probe, count=8)['current']
        pp = positive_current(model, np.exp(1j*(theta+step*remote)), 6, probe)
        pm = positive_current(model, np.exp(1j*(theta-step*remote)), 6, probe)
        rfd, pfd = (rp-rm)/(2*step), (pp-pm)/(2*step)
        difference_rows.append(dict(step=step, radial_difference=rfd, positive_difference=pfd,
                                    radial_error=abs(rfd-quadrature_rows[-1]['eight_node_response']),
                                    positive_error=abs(pfd-rows[-1]['terms'][-1]['positive_response'])))
    assert difference_rows[-1]['radial_error'] < 1e-12
    assert difference_rows[-1]['positive_error'] < 1e-9
    assert abs(rows[-1]['positive_hypercharge_response']) > 1e-6
    assert abs(rows[-1]['radial_hypercharge_response']) < 1e-10
    assert rows[-1]['charge_six_dirac_gap'] < .14
    assert min(term['kernel_gap'] for row in rows for term in row['terms']) > .9
    return dict(lattice_family="2 x 2 x 2 x T, antiperiodic time fermions", random_seed=2026090902,
                probe_link=dict(direction=0, head=[0, 0, 0, 0]),
                remote_link=dict(direction=1, head="[0,0,0,T/2]"),
                rows=rows, final_volume_quadrature=quadrature_rows, final_volume_differences=difference_rows,
                limitation="finite diagnostics, not an asymptotic positive-current no-go or a physical 4D continuum")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/radial_measure_audit.json'))
    args = parser.parse_args()
    report = dict(exact=exact_checks(), differential=differential_checks(), ward=ward_and_scaling_checks(),
                  closing_gap=closing_gap_scan(), arithmetic="exact controls and float64 diagnostics are separate")
    root = Path(__file__).resolve().parents[1]
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [
        'UnifiedTheory/Audit/KFCausalRadialMeasure.lean', 'scripts/radial_measure_audit.py',
        'scripts/positive_measure_audit.py', 'scripts/gauge_dressed_measure_audit.py',
        'scripts/chiral_measure_audit.py', 'scripts/overlap_chirality_audit.py']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
