#!/usr/bin/env python3
"""External non-Abelian gauge coupling for the specified Weyl walk.

Finite SU(2) tests use exact Gaussian-rational matrices. A separate larger
lattice check is numerical. Links are supplied external fields, not a
quantized Yang-Mills dynamics or a Standard Model derivation.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s
from weyl_walk_audit import PAULI, equal

I2 = s.eye(2)
X, Y, Z = PAULI
PLUS = [(I2+p)/2 for p in PAULI]
ROT = [(3*I2-4*s.I*p)/5 for p in PAULI]
PALETTE = [I2, *ROT, ROT[0]*ROT[1]]


def same(a, b):
    difference = a-b
    entries = difference.todok().values() if isinstance(difference, s.SparseMatrix) else difference
    assert all(s.expand(v) == 0 for v in entries), "Exact matrix equality failed"


def clean(a):
    return s.SparseMatrix(a.applyfunc(s.expand))


def kron(a, b):
    return s.SparseMatrix(s.kronecker_product(a, b))


def lattice(length):
    sites = list(itertools.product(range(length), repeat=3))
    index = {x: i for i, x in enumerate(sites)}
    shifts = []
    for axis in range(3):
        shifts.append([index[tuple((x[j]+(j == axis)) % length for j in range(3))]
                       for x in sites])
    return sites, shifts


def diagonal(blocks):
    return s.SparseMatrix(s.diag(*blocks))


def transport(shift, links):
    entries = {}
    for source, dest in enumerate(shift):
        for a in range(2):
            for b in range(2):
                value = links[dest][a, b]
                if value:
                    entries[(2*dest+a, 2*source+b)] = value
    return s.SparseMatrix(2*len(shift), 2*len(shift), entries)


def transform_links(shift, links, gauges):
    inverse = {dest: source for source, dest in enumerate(shift)}
    return [clean(g*link*gauges[inverse[x]].H) for x, (g, link) in enumerate(zip(gauges, links))]


def assemble(shifts, links, temporal):
    transports = [transport(p, l) for p, l in zip(shifts, links)]
    controls = [clean(kron(p, t)+kron(I2-p, t.H)) for p, t in zip(PLUS, transports)]
    spatial = clean(controls[2]*controls[1]*controls[0])
    return clean(kron(I2, diagonal(temporal))*spatial), spatial, transports, controls


def site_spin_state(psi, x, count):
    block = s.Matrix(2, 2, lambda spin, color: psi[spin*2*count+2*x+color, 0])
    return clean(block*block.H)


def exact_lattice_checks():
    sites, shifts = lattice(2)
    count, dimension = len(sites), 4*len(sites)
    gauges = [[PALETTE[(3*x+2*t+2) % len(PALETTE)] for x in range(count)] for t in range(4)]
    psi = s.SparseMatrix(dimension, 1, {(0, 0): 1, (7, 0): s.I, (21, 0): 2})
    psi_g = kron(I2, diagonal(gauges[0]))*psi
    total = s.eye(dimension)
    total_g = s.eye(dimension)
    operator_checks, local_checks = 0, 0
    wrong_squared_norm = None
    for t in range(3):
        links = [[PALETTE[(x*(j+1)+j+t) % len(PALETTE)] for x in range(count)] for j in range(3)]
        temporal = [PALETTE[(2*x+3*t+1) % len(PALETTE)] for x in range(count)]
        links_g = [transform_links(p, l, gauges[t]) for p, l in zip(shifts, links)]
        temporal_g = [clean(gauges[t+1][x]*temporal[x]*gauges[t][x].H) for x in range(count)]
        f, spatial, transports, controls = assemble(shifts, links, temporal)
        fg, _, _, _ = assemble(shifts, links_g, temporal_g)
        g0, g1 = [kron(I2, diagonal(g)) for g in gauges[t:t+2]]
        same(fg, g1*f*g0.H)
        same(f.H*f, s.eye(dimension))
        same(f*f.H, s.eye(dimension))
        operator_checks += 3
        for j, (transport_j, controlled_j) in enumerate(zip(transports, controls)):
            same(transport_j.H*transport_j, s.eye(2*count))
            same(transport_j*transport_j.H, s.eye(2*count))
            same(controlled_j.H*controlled_j, s.eye(dimension))
            same(transport(shifts[j], links_g[j]),
                 diagonal(gauges[t])*transport_j*diagonal(gauges[t]).H)
            operator_checks += 4
        if t == 0:
            wrong, _, _, _ = assemble(shifts, links_g, temporal)
            defect = clean(wrong-g1*f*g0.H)
            wrong_squared_norm = s.expand((defect.H*defect).trace())
            assert wrong_squared_norm > 0
        psi, psi_g = clean(f*psi), clean(fg*psi_g)
        same(psi_g, g1*psi)
        total, total_g = clean(f*total), clean(fg*total_g)
        same(total_g, g1*total*kron(I2, diagonal(gauges[0])).H)
        for x in range(count):
            same(site_spin_state(psi, x, count), site_spin_state(psi_g, x, count))
            local_checks += 1
        assert s.expand((psi.H*psi)[0]) == 6
    # A nonzero non-Abelian Wilson loop with no spatial variation.
    tx = transport(shifts[0], [ROT[0]]*count)
    ty = transport(shifts[1], [ROT[1]]*count)
    loop = clean(tx*ty*tx.H*ty.H)
    g = diagonal(gauges[0])
    txg, tyg = clean(g*tx*g.H), clean(g*ty*g.H)
    loop_g = clean(txg*tyg*txg.H*tyg.H)
    same(loop_g, g*loop*g.H)
    traces = []
    for x in range(count):
        block, block_g = loop[2*x:2*x+2, 2*x:2*x+2], loop_g[2*x:2*x+2, 2*x:2*x+2]
        assert s.expand(block.trace()) == s.expand(block_g.trace()) == s.Rational(226, 625)
        traces.append(str(s.expand(block.trace())))
    # Pure gauge backgrounds are exactly conjugate to the free update.
    free, _, _, _ = assemble(shifts, [[I2]*count for _ in range(3)], [I2]*count)
    pure_links = [transform_links(p, [I2]*count, gauges[0]) for p in shifts]
    pure, _, _, _ = assemble(shifts, pure_links, [I2]*count)
    full_g = kron(I2, diagonal(gauges[0]))
    same(pure, full_g*free*full_g.H)
    same(pure**3, full_g*(free**3)*full_g.H)
    return dict(lattice=[2, 2, 2], dimension=dimension, time_steps=3,
                exact_unitarity_and_step_covariance_checks=operator_checks,
                site_spin_density_checks=local_checks, initial_squared_norm=6,
                temporal_link_omission_covariance_defect_squared=str(wrong_squared_norm),
                wilson_traces=traces, nontrivial_wilson_defect=str(2-s.Rational(226, 625)),
                pure_gauge_similarity_and_powers=True,
                finite_volume_note="opposite nearest neighbors coincide on the two-site axes; larger lattice checked separately")


def continuum_checks():
    a = s.symbols("a", real=True)
    k = [s.Rational(2, 7), -s.Rational(1, 3), s.Rational(4, 9)]
    strengths = [s.Rational(1, 5), -s.Rational(2, 7), s.Rational(3, 8)]
    a0 = s.Rational(4, 11)*Y
    controls = []
    for p, q, strength, axis in zip(PLUS, k, strengths, PAULI):
        link = s.cos(a*strength)*I2-s.I*s.sin(a*strength)*axis
        phase = s.cos(a*q)-s.I*s.sin(a*q)
        transport_j = phase*link
        controls.append(s.kronecker_product(p, transport_j)+
                        s.kronecker_product(I2-p, transport_j.H))
    temporal = s.kronecker_product(I2, s.cos(a*s.Rational(4, 11))*I2-
                                   s.I*s.sin(a*s.Rational(4, 11))*Y)
    # Differentiate the actual factors; the product rule then supplies
    # the whole step derivative since every factor is identity at zero.
    factors = [temporal, controls[2], controls[1], controls[0]]
    derivative = s.zeros(4)
    for f in factors:
        equal(f.subs(a, 0), s.eye(4))
        derivative += s.diff(f, a).subs(a, 0)
    h = s.kronecker_product(I2, a0)+sum(
        (s.kronecker_product(axis, q*I2+strength*axis)
         for q, strength, axis in zip(k, strengths, PAULI)), s.zeros(4))
    equal(derivative, -s.I*h)
    lx = s.cos(a*strengths[0])*I2-s.I*s.sin(a*strengths[0])*X
    ly = s.cos(a*strengths[1])*I2-s.I*s.sin(a*strengths[1])*Y
    curvature_loop = lx*ly*lx.H*ly.H
    commutator = strengths[0]*strengths[1]*(X*Y-Y*X)
    equal(s.diff(curvature_loop, a, 2).subs(a, 0)/2, -commutator)
    return dict(arithmetic="exact symbolic derivatives at zero",
                noncommuting_constant_background_generator=True,
                constant_field_plaquette_second_order=True,
                hamiltonian=[[str(v) for v in h.row(j)] for j in range(4)],
                scope="constant supplied SU(2) potentials; variable-field continuum derivation in note")


def numerical_larger_lattice():
    sites, shifts = lattice(3)
    count, dimension = len(sites), 4*len(sites)
    palette = [np.array(p, dtype=complex) for p in PALETTE]
    plus = [np.array(p, dtype=complex) for p in PLUS]
    def diag(blocks):
        out = np.zeros((2*count, 2*count), complex)
        for x, block in enumerate(blocks):
            out[2*x:2*x+2, 2*x:2*x+2] = block
        return out
    def trans(p, links):
        out = np.zeros((2*count, 2*count), complex)
        for source, dest in enumerate(p):
            out[2*dest:2*dest+2, 2*source:2*source+2] = links[dest]
        return out
    def assemble_np(links, temporal):
        controls = []
        for p, shift, ls in zip(plus, shifts, links):
            t = trans(shift, ls)
            controls.append(np.kron(p, t)+np.kron(np.eye(2)-p, t.conj().T))
        return np.kron(np.eye(2), diag(temporal))@controls[2]@controls[1]@controls[0]
    g0 = [palette[(2*x+1) % len(palette)] for x in range(count)]
    g1 = [palette[(3*x+2) % len(palette)] for x in range(count)]
    links = [[palette[(x*(j+1)+j) % len(palette)] for x in range(count)] for j in range(3)]
    temporal = [palette[(x+2) % len(palette)] for x in range(count)]
    links_g = []
    for shift, ls in zip(shifts, links):
        inverse = {dest: source for source, dest in enumerate(shift)}
        links_g.append([g0[x]@ls[x]@g0[inverse[x]].conj().T for x in range(count)])
    temporal_g = [g1[x]@temporal[x]@g0[x].conj().T for x in range(count)]
    f, fg = assemble_np(links, temporal), assemble_np(links_g, temporal_g)
    g0m, g1m = [np.kron(np.eye(2), diag(g)) for g in (g0, g1)]
    defects = dict(unitarity=float(np.linalg.norm(f.conj().T@f-np.eye(dimension))),
                   spacetime_covariance=float(np.linalg.norm(fg-g1m@f@g0m.conj().T)))
    assert max(defects.values()) < 1e-11
    return dict(lattice=[3, 3, 3], dimension=dimension,
                arithmetic="complex128 Frobenius residuals, not certified bounds", **defects)


def numerical_constant_field_convergence():
    """Check the analytic t^2 K^2/n bound on actual SU(2) walk factors."""
    pauli = [np.array(p, dtype=complex) for p in PAULI]
    plus = [(np.eye(2)+p)/2 for p in pauli]
    momenta = [2/7, -1/3, 4/9]
    strengths = [1/5, -2/7, 3/8]
    scalar_strength = 4/11
    h = np.kron(np.eye(2), scalar_strength*pauli[1])
    for p, q, strength in zip(pauli, momenta, strengths):
        h += np.kron(p, q*np.eye(2)+strength*p)
    eigenvalues, eigenvectors = np.linalg.eigh(h)
    norm_budget = scalar_strength+sum(abs(q)+abs(v) for q, v in zip(momenta, strengths))
    cases = []
    for time in [0.25, 0.75, 2.0]:
        exact = (eigenvectors*np.exp(-1j*time*eigenvalues))@eigenvectors.conj().T
        for steps in [1, 2, 4, 8, 16, 32, 64, 128]:
            a = time/steps
            factors = []
            for p, axis, q, strength in zip(plus, pauli, momenta, strengths):
                link = np.cos(a*strength)*np.eye(2)-1j*np.sin(a*strength)*axis
                transport_j = np.exp(-1j*a*q)*link
                factors.append(np.kron(p, transport_j)+np.kron(np.eye(2)-p, transport_j.conj().T))
            temporal = np.kron(np.eye(2), np.cos(a*scalar_strength)*np.eye(2)-
                               1j*np.sin(a*scalar_strength)*pauli[1])
            f = temporal@factors[2]@factors[1]@factors[0]
            error = float(np.linalg.norm(np.linalg.matrix_power(f, steps)-exact, ord=2))
            bound = time*time*norm_budget*norm_budget/steps
            assert error <= bound+1e-12
            cases.append(dict(time=time, steps=steps, error=error, analytic_bound=bound))
    return dict(arithmetic="complex128 checks of an analytic bound; not interval certification",
                cases_checked=len(cases), norm_budget=norm_budget,
                max_error_to_bound_ratio=max(c["error"]/c["analytic_bound"] for c in cases),
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = dict(scope="external non-Abelian gauge-coupled Weyl walk; no gauge-field dynamics or TOE closure",
                  sympy_version=s.__version__, numpy_version=np.__version__,
                  exact_lattice=exact_lattice_checks(), continuum=continuum_checks(),
                  numerical_lattice=numerical_larger_lattice(),
                  constant_field_convergence=numerical_constant_field_convergence())
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/gauge_walk_audit.py", "scripts/weyl_walk_audit.py",
             "UnifiedTheory/Audit/KFCausalGaugeWalk.lean",
             "UnifiedTheory/Audit/KFCausalWeylWalk.lean"]
    result["source_sha256"] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    print("All exact and numerical gauge-walk checks passed within their stated scope.")


if __name__ == "__main__":
    main()
