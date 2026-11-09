#!/usr/bin/env python3
"""Local chiral frames and determinant transport; no global gauge measure claim.

Exact SymPy checks are separated from floating-point overlap experiments.
Run with OPENBLAS_NUM_THREADS=1 for predictable small-matrix performance.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s

from overlap_chirality_audit import GAMMA, GAMMA5, equal


def exact_loop():
    phi = s.symbols("phi", real=True)
    eye = s.eye(2)
    v0 = s.Matrix([s.sqrt(3)/2, s.Rational(1, 2)])
    p0 = v0*v0.H
    rotation = s.diag(1, s.exp(s.I*phi))
    v = rotation*v0
    p = v*v.H
    dp = s.diff(p, phi)
    k = dp*p-p*dp
    q = rotation*(s.exp(-s.I*phi/4)*p0+s.exp(-3*s.I*phi/4)*(eye-p0))
    equal(q.H*q, eye)
    equal(s.diff(q, phi), k*q)
    equal(p*q, q*p0)
    equal(q.subs(phi, 0), eye)
    equal(p.subs(phi, 2*s.pi), p0)
    equal(q.subs(phi, 2*s.pi), -s.I*p0+s.I*(eye-p0))
    connection = s.simplify(s.I*(v.H*s.diff(v, phi))[0])
    assert connection == -s.Rational(1, 4)
    holonomy = s.simplify((v0.H*q.subs(phi, 2*s.pi)*v0)[0])
    assert holonomy == -s.I
    assert s.exp(s.I*s.integrate(connection, (phi, 0, 2*s.pi))) == holonomy
    assert s.simplify((eye-p0+p0*q.subs(phi, 2*s.pi)).det()) == holonomy
    # The entire non-flat loop fits in one reference-frame patch.
    equal((p-p0)*(p-p0), s.Rational(3, 4)*s.sin(phi/2)**2*eye)
    gram = s.simplify((v0.H*p*v0)[0].expand(complex=True))
    assert s.trigsimp(gram-(1-s.Rational(3, 4)*s.sin(phi/2)**2)) == 0
    # Curvature for commuting coordinates of CP^1, computed from projectors.
    x, y = s.symbols("x y", real=True)
    z = s.Matrix([1, x+s.I*y])
    pxy = z*z.H/(1+x*x+y*y)
    px, py = s.diff(pxy, x), s.diff(pxy, y)
    curvature = s.simplify(s.I*(pxy*(px*py-py*px)).trace())
    assert s.simplify(curvature+2/(1+x*x+y*y)**2) == 0
    complement = s.simplify(s.I*((eye-pxy)*(px*py-py*px)).trace())
    assert s.simplify(curvature+complement) == 0
    # A flat connection on a circle can still violate global integrability.
    flat_phase = s.exp(s.I*s.integrate(s.Rational(1, 2), (phi, 0, 2*s.pi)))
    assert flat_phase == -1  # constant P has Kato transport I instead
    # Exact universal margins for all arrays |base|<=3/25, |first|,|second|<=1,
    # using sqrt(2)<10/7 and radius 9/200. These need no numerical spectral fit.
    assert s.Rational(10, 7)**2 > 2
    eta_upper = 4*s.Rational(3, 25)+4*s.Rational(10, 7)*s.Rational(9, 200)
    rho_upper = 4*s.Rational(10, 7)*s.Rational(9, 200)/(1-eta_upper)
    assert eta_upper == s.Rational(129, 175)
    assert rho_upper == s.Rational(45, 46)
    assert 1-rho_upper**2 == s.Rational(91, 2116)
    # Direct rotation and frame transition: exact rational projectors.
    frames = [s.Matrix([1, 0]), s.Matrix([3, 4])/5, s.Matrix([3, 4*s.I])/5]
    for a, b in itertools.product(frames, repeat=2):
        pa, pb = a*a.H, b*b.H
        bridge = pb*pa+(eye-pb)*(eye-pa)
        equal(bridge.H*bridge, eye-(pa-pb)*(pa-pb))
        equal(pb*bridge, bridge*pa)
    # Orthogonality to the reference makes the patch construction singular.
    assert (frames[0].H*s.diag(0, 1)*frames[0])[0] == 0
    return dict(arithmetic="exact symbolic matrices, differentiation, integration",
                ambient_dimension=2, chiral_rank=1,
                periodic_frame_connection=str(connection), kato_holonomy=str(holonomy),
                projector_loop_closes=True, kato_ode_verified=True,
                zero_connection_holonomy="1 (fails against -I)",
                max_projector_distance="sqrt(3)/2", minimum_reference_gram="1/4",
                coordinate_curvature=str(curvature), complement_curvature_cancels=True,
                flat_circle_negative_control=dict(curvature="0", kato_holonomy="1",
                                                 candidate_connection_holonomy=str(flat_phase)),
                universal_disk_scalar_bounds=dict(eta_upper=str(eta_upper), gap_lower="46/175",
                                                  projector_distance_upper=str(rho_upper),
                                                  gram_lower="91/2116"),
                orthogonal_reference_negative_control=True,
                scope="projector geometry example, not a lattice gauge anomaly")


def inverse_sqrt(a):
    vals, vecs = np.linalg.eigh((a+a.conj().T)/2)
    assert vals[0] > 0
    return (vecs/np.sqrt(vals))@vecs.conj().T, float(vals[0])


class OverlapFamily:
    """Four-dimensional periodic Wilson kernel, external charge-one U(1) links."""
    def __init__(self, length=2):
        self.sites = list(itertools.product(range(length), repeat=4))
        self.count = len(self.sites)
        self.dimension = 4*self.count
        indices = {x: j for j, x in enumerate(self.sites)}
        self.previous = []
        for mu in range(4):
            self.previous.append(np.array([
                indices[tuple((v-1) % length if j == mu else v for j, v in enumerate(x))]
                for x in self.sites]))
        self.eye = np.eye(self.dimension, dtype=complex)
        self.g5 = np.kron(np.array(GAMMA5, complex), np.eye(self.count))
        self.plus = [(np.eye(4)+np.array(g, complex))/2 for g in GAMMA]
        self.minus = [np.eye(4)-p for p in self.plus]
        rng = np.random.default_rng(9811032)
        self.base = rng.uniform(-0.12, 0.12, (4, self.count))
        self.first = rng.uniform(-1, 1, self.base.shape)
        self.second = rng.uniform(-1, 1, self.base.shape)
        self.radius = 0.045

    def kernel(self, x, y, gauge=None, derivatives=False):
        theta = self.base+x*self.first+y*self.second
        if gauge is not None:
            theta = theta+np.array([gauge-gauge[p] for p in self.previous])
        h = 3*self.eye.copy()  # D_W-I = 3I - sum(S_mu)
        dx, dy = np.zeros_like(h), np.zeros_like(h)
        for mu in range(4):
            t = np.zeros((self.count, self.count), complex)
            t[np.arange(self.count), self.previous[mu]] = np.exp(1j*theta[mu])
            h -= np.kron(self.plus[mu], t)+np.kron(self.minus[mu], t.conj().T)
            if derivatives:
                for tangent, target in [(self.first, dx), (self.second, dy)]:
                    dt = 1j*tangent[mu, :, None]*t
                    target -= np.kron(self.plus[mu], dt)+np.kron(self.minus[mu], dt.conj().T)
        return self.g5@h, self.g5@dx, self.g5@dy

    def evaluate(self, x, y, gauge=None, derivatives=False):
        h, dx, dy = self.kernel(x, y, gauge, derivatives)
        assert np.linalg.norm(h-h.conj().T) < 1e-12
        vals, vecs = np.linalg.eigh(h)
        positive = vals > 0
        v = vecs[:, positive]
        p = v@v.conj().T  # hat P_minus = (I + sign H_W)/2
        gap = float(np.min(np.abs(vals)))
        answer = dict(p=p, v=v, complement=vecs[:, ~positive], gap=gap)
        if derivatives:
            # Divided differences of the spectral projector: only opposite-sign
            # eigenvalue pairs contribute, whose denominators are gap-protected.
            mask = positive[:, None] != positive[None, :]
            divided = np.zeros((len(vals), len(vals)))
            numerator = positive.astype(float)[:, None]-positive.astype(float)[None, :]
            denominator = vals[:, None]-vals[None, :]
            divided[mask] = numerator[mask]/denominator[mask]
            a, b = [vecs@(divided*(vecs.conj().T@dh@vecs))@vecs.conj().T for dh in [dx, dy]]
            curvature = 1j*np.trace(p@(a@b-b@a))
            assert abs(curvature.imag) < 1e-10
            answer.update(a=a, b=b, curvature=float(curvature.real))
        return answer


def determinant_transport(frames):
    """Discrete direct-rotation determinant; converges to Kato transport.

    Product orientation is next†previous, giving exp(i integral i Tr V†dV).
    A periodic change of basis telescopes exactly even at finite step count.
    """
    phase = 1+0j
    smallest = 1.0
    for previous, following in zip(frames, frames[1:]+frames[:1]):
        u, sigma, vh = np.linalg.svd(following.conj().T@previous)
        phase *= np.linalg.det(u@vh)
        smallest = min(smallest, float(sigma[-1]))
    return phase/abs(phase), smallest


def numerical_overlap():
    family = OverlapFamily()
    r = family.radius
    reference = family.evaluate(r, 0)
    w0, p0 = reference['v'], reference['p']
    # Bounds hold on the whole disk, not just on the sampled circle.
    theta_max = np.abs(family.base)+r*np.sqrt(family.first**2+family.second**2)
    eta_bound = float(np.max(theta_max, axis=1).sum())  # |exp(i theta)-1| <= |theta|
    assert eta_bound < 1
    # Sylvester bound ||dP|| <= ||dH||/(2g), along a disk chord of length <=2r.
    # Each of four link directions has tangent norm <=sqrt(2).
    patch_distance_bound = 4*np.sqrt(2)*r/(1-eta_bound)
    assert patch_distance_bound < 1
    rows = []
    all_residuals = []
    gauge = np.linspace(-1.3, 1.7, family.count)
    g = np.kron(np.eye(4), np.diag(np.exp(1j*gauge)))
    for count in [32, 64, 128, 256]:
        frames, complements, rebased, transformed = [], [], [], []
        min_gap, min_gram, max_distance = 9., 1., 0.
        for j in range(count):
            phi = 2*np.pi*j/count
            x, y = r*np.cos(phi), r*np.sin(phi)
            data = family.evaluate(x, y)
            p = data['p']
            factor, gram_min = inverse_sqrt(w0.conj().T@p@w0)
            v = p@w0@factor
            min_gap, min_gram = min(min_gap, data['gap']), min(min_gram, gram_min)
            distance = float(np.linalg.norm(p-p0, 2))
            max_distance = max(max_distance, distance)
            assert gram_min >= 1-distance**2-2e-12
            all_residuals.extend([float(np.linalg.norm(v.conj().T@v-np.eye(v.shape[1]))),
                                  float(np.linalg.norm(v@v.conj().T-p))])
            frames.append(v)
            complements.append(data['complement'])
            phases = np.exp(1j*(np.arange(v.shape[1])+1)*np.sin(phi)/5)
            rebased.append(v*phases)
            # Independent endpoint-link rebuild with a fixed-in-parameter gauge change.
            if count == 32:
                pg = family.evaluate(x, y, gauge=gauge)['p']
                sg, _ = inverse_sqrt((g@w0).conj().T@pg@(g@w0))
                vg = pg@(g@w0)@sg
                transformed.append(vg)
                all_residuals.extend([float(np.linalg.norm(pg-g@p@g.conj().T)),
                                      float(np.linalg.norm(vg-g@v))])
        phase, min_overlap = determinant_transport(frames)
        opposite, _ = determinant_transport(complements)
        rephase, _ = determinant_transport(rebased)
        all_residuals.extend([float(abs(phase*opposite-1)), float(abs(phase-rephase))])
        if transformed:
            gphase, _ = determinant_transport(transformed)
            all_residuals.append(float(abs(phase-gphase)))
        rows.append(dict(steps=count, phase_radians=float(np.angle(phase)),
                         minimum_kernel_gap=min_gap, minimum_reference_gram=min_gram,
                         maximum_reference_projector_distance=max_distance,
                         minimum_neighbor_frame_singular_value=min_overlap,
                         complement_phase_radians=float(np.angle(opposite))))
    # Independent disk integral of projector curvature (polar Gauss quadrature).
    integrals = []
    for radial_count, angular_count in [(4, 16), (8, 32)]:
        nodes, weights = np.polynomial.legendre.leggauss(radial_count)
        integral = 0.
        for node, weight in zip(nodes, weights):
            radius = r*(node+1)/2
            for phi in np.arange(angular_count)*2*np.pi/angular_count:
                datum = family.evaluate(radius*np.cos(phi), radius*np.sin(phi), derivatives=True)
                integral += weight*r/2*radius*2*np.pi/angular_count*datum['curvature']
        integrals.append(float(integral))
    center = family.evaluate(0, 0, derivatives=True)
    # Check the spectral derivative against an independent central difference.
    derivative_errors = []
    for step in [1e-3, 5e-4]:
        finite = (family.evaluate(step, 0)['p']-family.evaluate(-step, 0)['p'])/(2*step)
        derivative_errors.append(float(np.linalg.norm(finite-center['a'])))
    assert derivative_errors[1] < 0.3*derivative_errors[0]
    for a in [center['a'], center['b']]:
        p = center['p']
        k = a@p-p@a
        all_residuals.extend([float(np.linalg.norm(a@p+p@a-a)),
                              float(np.linalg.norm(k@p-p@k-a))])
    x_generator = 1j*np.kron(np.eye(4), np.diag(gauge))
    p, b = center['p'], center['b']
    a = x_generator@p-p@x_generator
    all_residuals.append(float(abs(1j*np.trace(p@(a@b-b@a))+1j*np.trace(x_generator@b))))
    assert max(all_residuals) < 1e-10
    assert min(row['minimum_kernel_gap'] for row in rows) >= 1-eta_bound
    assert max(row['maximum_reference_projector_distance'] for row in rows) < patch_distance_bound
    errors = [abs(row['phase_radians']-integrals[-1]) for row in rows]
    assert abs(integrals[-1]-integrals[-2]) < 1e-10
    assert abs(integrals[-1]) > 1e-9, "Loop must distinguish zero connection from actual curvature"
    assert errors[-1] < errors[0]/30
    return dict(arithmetic="float64; no interval certification", group="external U(1), charge 1",
                lattice="periodic 2^4", ambient_dimension=family.dimension, chiral_rank=w0.shape[1],
                random_seed=9811032, radius=r, uniform_weak_field_eta_bound=eta_bound,
                analytic_disk_kernel_gap_lower_bound=1-eta_bound, loop_refinements=rows,
                analytic_disk_patch_distance_upper_bound=float(patch_distance_bound),
                analytic_disk_reference_gram_lower_bound=float(1-patch_distance_bound**2),
                curvature_disk_integrals=integrals, transport_vs_curvature_errors=errors,
                central_difference_projector_derivative_errors=derivative_errors,
                maximum_identity_residual=max(all_residuals),
                periodic_basis_change_check=True, fixed_gauge_rebuild_check=True,
                complementary_transport_cancellation=True,
                scope="local frame and contractible loop; no physical measure current or anomaly cancellation")


def hypercharge_curvature():
    """Vanishing representation coefficients do not set finite-lattice curvature to zero."""
    # All left-handed convention, integer q=6Y; colors/weak components are copies
    # because the non-Abelian background fields are set to the identity here.
    species = [('Q', 1, 6), ('uc', -4, 3), ('dc', 2, 3), ('L', -3, 2), ('ec', 6, 1)]
    linear = sum(m*q for _, q, m in species)
    cubic = sum(m*q**3 for _, q, m in species)
    assert linear == cubic == 0
    rows = []
    for denominator in [6, 12, 24]:
        terms, gaps = [], []
        for name, charge, multiplicity in species:
            family = OverlapFamily()
            for attribute in ['base', 'first', 'second']:
                setattr(family, attribute, getattr(family, attribute)*charge/denominator)
            datum = family.evaluate(0, 0, derivatives=True)
            terms.append(dict(species=name, integer_hypercharge=charge,
                              multiplicity=multiplicity, curvature=datum['curvature']))
            gaps.append(datum['gap'])
        total = sum(term['multiplicity']*term['curvature'] for term in terms)
        rows.append(dict(field_scale_denominator=denominator, species=terms,
                         weighted_curvature=total, minimum_kernel_gap=min(gaps)))
    assert abs(rows[0]['weighted_curvature']) > 1e-6
    return dict(coefficient_arithmetic="exact integers", sum_m_q=linear, sum_m_q_cubed=cubic,
                matrix_arithmetic="float64, no interval certification", samples=rows,
                interpretation="zero measure connection fails the sampled finite-lattice curvature condition",
                limitations="no anomaly of the SM inferred; no continuum scaling theorem, local current, or global measure constructed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/chiral_measure_audit.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = dict(exact=exact_loop(), numerical=numerical_overlap(),
                  hypercharge=hypercharge_curvature())
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [
        'UnifiedTheory/Audit/KFCausalChiralMeasure.lean', 'scripts/chiral_measure_audit.py',
        'scripts/overlap_chirality_audit.py']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
