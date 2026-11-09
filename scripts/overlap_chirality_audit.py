#!/usr/bin/env python3
"""Overlap chiral algebra, exact free poles, and external SU(2) covariance.

The Dirac operator is a Euclidean regulator, not a real-time walk. Exact
symbolic checks are separate from numerical sign-function checks. There
is no dynamical gauge-field measure or anomaly-cancellation proof here.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s

X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)
PAULI = [X, Y, Z]
GAMMA = [s.kronecker_product(X, p) for p in PAULI]+[s.kronecker_product(Y, s.eye(2))]
GAMMA5 = s.kronecker_product(Z, s.eye(2))


def equal(a, b):
    assert all(s.simplify(v) == 0 for v in a-b), "Exact matrix identity failed"


def symbolic_checks():
    eye = s.eye(4)
    for j, g in enumerate(GAMMA):
        equal(g.H, g)
        equal(g*g, eye)
        equal(g*GAMMA5+GAMMA5*g, s.zeros(4))
        for k in range(j):
            equal(g*GAMMA[k]+GAMMA[k]*g, s.zeros(4))
    equal(GAMMA5.H, GAMMA5)
    equal(GAMMA5*GAMMA5, eye)
    components = s.symbols("s0:4", real=True)
    b = s.symbols("B", real=True)
    w = s.symbols("w", positive=True)
    kinetic = sum((x*g for x, g in zip(components, GAMMA)), s.zeros(4))
    a = b*eye+s.I*kinetic
    squared = b*b+sum(x*x for x in components)
    equal(a.H*a, squared*eye)
    equal(GAMMA5*a*GAMMA5, a.H)
    d = eye+a/w
    equal(w*w*(GAMMA5*d+d*GAMMA5-d*GAMMA5*d), (w*w-squared)*GAMMA5)
    equal(d.H*d, (1+2*b/w+squared/(w*w))*eye)
    hats = GAMMA5*(eye-d)
    equal(hats.H, hats)
    equal(hats*hats, squared/(w*w)*eye)

    spacing = s.symbols("a", real=True)
    momenta = s.symbols("k0:4", real=True)
    mass = sum(1-s.cos(spacing*k) for k in momenta)-1
    sine = [s.sin(spacing*k) for k in momenta]
    radius = s.sqrt(mass*mass+sum(x*x for x in sine))
    actual = eye+(mass*eye+s.I*sum((x*g for x, g in zip(sine, GAMMA)), s.zeros(4)))/radius
    equal(actual.subs(spacing, 0), s.zeros(4))
    equal(s.diff(actual, spacing).subs(spacing, 0),
          s.I*sum((k*g for k, g in zip(momenta, GAMMA)), s.zeros(4)))
    corners = []
    for bits in itertools.product([0, 1], repeat=4):
        mass_value = 2*sum(bits)-1
        overlap = eye+(s.Rational(mass_value, abs(mass_value)))*eye
        expected = s.zeros(4) if sum(bits) == 0 else 2*eye
        equal(overlap, expected)
        # Merely reinterpreting I-D as a unitary step leaves pi nodes.
        polar_step = eye-overlap
        equal(polar_step, eye if sum(bits) == 0 else -eye)
        corners.append(dict(pi_coordinates=list(bits), wilson_mass=mass_value,
                            overlap_value="0" if sum(bits) == 0 else "2 I",
                            polar_step_value="I" if sum(bits) == 0 else "-I"))
    return dict(arithmetic="exact symbolic matrices and derivatives",
                clifford_algebra=True, overlap_norm_identity=True,
                ginsparg_wilson_defect_identity=True, continuum_generator=True,
                corners=corners, free_dirac_zero_corners=1,
                polar_reinterpretation_pi_corners=15,
                polar_three_spatial_slice_pi_corners=sum(
                    c["pi_coordinates"][3] == 0 and c["polar_step_value"] == "-I" for c in corners),
                completeness="analytic sine-zero and Wilson-mass argument, not a momentum scan")


def fixed_filter_check():
    projector = s.ones(4, 4)/4  # retain only the zero-momentum mode
    gauge = s.diag(1, -1, 1, -1)
    psi = s.ones(4, 1)/2
    equal(projector*projector, projector)
    equal(projector*psi, psi)
    equal(gauge.H*gauge, s.eye(4))
    equal(projector*gauge*psi, s.zeros(4, 1))
    leakage = ((s.eye(4)-projector)*gauge*psi).norm()**2
    comm = projector*gauge-gauge*projector
    defect = s.expand((comm.H*comm).trace())
    assert leakage == 1 and defect == 2
    return dict(arithmetic="exact", sites=4, retained_momenta=1,
                gauge_transformed_state_leakage=str(leakage), commutator_squared_frobenius=str(defect))


def numerical_gauge_checks():
    length = 3
    sites = list(itertools.product(range(length), repeat=4))
    index = {x: i for i, x in enumerate(sites)}
    count = len(sites)
    dimension = 8*count
    pauli = [np.array(p, dtype=complex) for p in PAULI]
    gamma = [np.array(g, dtype=complex) for g in GAMMA]
    g5 = np.kron(np.array(GAMMA5, dtype=complex), np.eye(2*count))
    eye = np.eye(dimension, dtype=complex)
    weak = [np.eye(2)]+[(399*np.eye(2)-40j*p)/401 for p in pauli]
    strong = [np.eye(2)]+[(3*np.eye(2)-4j*p)/5 for p in pauli]
    strong.append(strong[1]@strong[2])
    shifts, links = [], []
    for axis in range(4):
        shifts.append([index[tuple((x[j]+(j == axis)) % length for j in range(4))] for x in sites])
        links.append([weak[(sum((j+1)*x[j] for j in range(4))+axis) % 4] for x in sites])
    frames = [strong[(sum((j+2)*x[j] for j in range(4))+1) % 5] for x in sites]
    frame = np.zeros((2*count, 2*count), complex)
    for j, g in enumerate(frames):
        frame[2*j:2*j+2, 2*j:2*j+2] = g
    full_frame = np.kron(np.eye(4), frame)
    changed_links = []
    for shift, ls in zip(shifts, links):
        inverse = {dest: source for source, dest in enumerate(shift)}
        changed_links.append([frames[x]@ls[x]@frames[inverse[x]].conj().T for x in range(count)])

    def wilson(ls):
        dw = np.zeros_like(eye)
        transports = []
        for g, shift, row in zip(gamma, shifts, ls):
            transport = np.zeros((2*count, 2*count), complex)
            for source, dest in enumerate(shift):
                transport[2*dest:2*dest+2, 2*source:2*source+2] = row[dest]
            plus = (np.eye(4)+g)/2
            controlled = np.kron(plus, transport)+np.kron(np.eye(4)-plus, transport.conj().T)
            dw += eye-controlled
            transports.append(transport)
        return g5@(dw-eye), transports

    h, transports = wilson(links)
    hg, _ = wilson(changed_links)
    residuals = dict(wilson_hermiticity=float(np.linalg.norm(h-h.conj().T)),
                     wilson_covariance=float(np.linalg.norm(hg-full_frame@h@full_frame.conj().T)))
    eigenvalues, eigenvectors = np.linalg.eigh(h)
    eigenvalues_g, eigenvectors_g = np.linalg.eigh(hg)
    eta = 8/np.sqrt(401)
    gap_bound = 1-eta
    upper_bound = 7+eta
    gap = float(np.min(np.abs(eigenvalues)))
    assert gap >= gap_bound-1e-12
    assert np.max(np.abs(eigenvalues)) <= upper_bound+1e-12
    assert np.min(np.abs(eigenvalues_g)) >= gap_bound-1e-12
    epsilon = (eigenvectors*np.sign(eigenvalues))@eigenvectors.conj().T
    epsilon_g = (eigenvectors_g*np.sign(eigenvalues_g))@eigenvectors_g.conj().T
    d, dg = eye+g5@epsilon, eye+g5@epsilon_g
    hat = -epsilon
    phat_minus = (eye-hat)/2
    phat_minus_g = (eye+epsilon_g)/2
    pplus = (eye+g5)/2
    residuals.update(
        sign_involution=float(np.linalg.norm(epsilon@epsilon-eye)),
        overlap_covariance=float(np.linalg.norm(dg-full_frame@d@full_frame.conj().T)),
        ginsparg_wilson=float(np.linalg.norm(g5@d+d@g5-d@g5@d)),
        gamma_hermiticity=float(np.linalg.norm(d.conj().T-g5@d@g5)),
        chirality_projector=float(np.linalg.norm(phat_minus@phat_minus-phat_minus)),
        chiral_intertwining=float(np.linalg.norm(d@phat_minus-pplus@d)),
        chiral_projector_covariance=float(np.linalg.norm(phat_minus_g-full_frame@phat_minus@full_frame.conj().T)))
    assert max(residuals.values()) < 5e-10
    loop = transports[0]@transports[1]@transports[0].conj().T@transports[1].conj().T
    loop_defect = float(np.linalg.norm(loop-np.eye(2*count)))
    assert loop_defect > 0.1

    # Eigenvalue evaluation of the explicit local polynomial approximants.
    # Locality/range follows analytically from the polynomial degree.
    ratio = 1-gap_bound**2/upper_bound**2
    x = 1-eigenvalues**2/upper_bound**2
    term = np.ones_like(x)
    partial = np.zeros_like(x)
    coefficient = 1.0
    approximation_checks = []
    for n in range(2049):
        partial += coefficient*term
        if n in [0, 8, 32, 128, 512, 2048]:
            approximated_sign = eigenvalues/upper_bound*partial
            error = float(np.max(np.abs(approximated_sign-np.sign(eigenvalues))))
            bound = float(ratio**(n+1)/(1-ratio))
            assert error <= bound+2e-12
            approximation_checks.append(dict(order=n, range_at_most=2*n+1,
                                             numerical_error=error, analytic_bound=bound))
        coefficient *= (2*n+1)/(2*n+2)
        term *= x
    return dict(arithmetic="complex128 eigendecomposition and Frobenius residuals; not interval certificates",
                lattice=[3]*4, dimension=dimension, colors=2,
                supplied_background="inhomogeneous weak SU(2) links; independent large local gauge transformation",
                analytic_gap_bound="1 - 8/sqrt(401)", numeric_gap_lower_bound=float(gap_bound),
                observed_kernel_gap=gap, residuals=residuals,
                wilson_loop_frobenius_defect=loop_defect,
                chiral_projector_change_under_gauge=float(np.linalg.norm(phat_minus_g-phat_minus)),
                local_polynomial_checks=approximation_checks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = dict(scope="overlap Euclidean chiral regulator; no completed Weyl gauge measure or TOE",
                  exact_free=symbolic_checks(), fixed_filter=fixed_filter_check(),
                  numerical_external_gauge=numerical_gauge_checks(),
                  sympy_version=s.__version__, numpy_version=np.__version__)
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/overlap_chirality_audit.py", "UnifiedTheory/Audit/KFCausalOverlapChirality.lean",
             "UnifiedTheory/Audit/KFCausalGaugeWalk.lean"]
    result["source_sha256"] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    print("All overlap-chirality checks passed within their stated exact or numerical scope.")


if __name__ == "__main__":
    main()
