#!/usr/bin/env python3
"""Reproducible SU(2) regression audit for GAUGE_DISCRETE_CONTINUUM.md.

Uses standard-library quaternions. Their Euclidean norm is exactly the
operator norm in the standard two-dimensional complex representation.
Exact Fraction checks and floating-point checks are reported separately.
Numerics supplement, and do not replace, the analytic or Lean proofs.
"""
from __future__ import annotations

import json
import math
import random
from fractions import Fraction
from pathlib import Path

ONE = (1, 0, 0, 0)
ZERO = (0, 0, 0, 0)


def mul(p, q):
    a, b, c, d = p
    e, f, g, k = q
    return (a*e-b*f-c*g-d*k, a*f+b*e+c*k-d*g,
            a*g-b*k+c*e+d*f, a*k+b*g-c*f+d*e)


def inv(q):
    # All inputs to inv are unit quaternions.
    return (q[0], -q[1], -q[2], -q[3])


def sub(p, q):
    return tuple(a-b for a, b in zip(p, q))


def norm(q):
    return math.sqrt(sum(float(a)**2 for a in q))


def exp_pure(v, t=1.0):
    r = math.sqrt(sum(a*a for a in v))
    s = t if r == 0 else math.sin(t*r)/r
    return (math.cos(t*r), *(s*a for a in v))


def conjugate(g, q):
    return mul(mul(g, q), inv(g))


def curvature(x, y):
    return (0.30+0.20*x, 0.15+0.25*y, 0.20+0.10*x*y)


def primitive(x, y):
    return (0.30*x+0.10*x*x, (0.15+0.25*y)*x, 0.20*x+0.05*x*x*y)


def plaquette(H, V, i, j):
    return mul(mul(mul(H[i, j], V[i+1, j]), inv(H[i, j+1])), inv(V[i, j]))


def axial_links(P, n):
    H = {(i, j): ONE for i in range(n) for j in range(n+1)}
    V = {}
    for j in range(n):
        V[0, j] = ONE
        for i in range(n):
            V[i+1, j] = mul(P[i, j], V[i, j])
    return H, V


def gauge_links(H, V, g):
    h = {(i, j): mul(mul(g[i, j], q), inv(g[i+1, j])) for (i, j), q in H.items()}
    v = {(i, j): mul(mul(g[i, j], q), inv(g[i, j+1])) for (i, j), q in V.items()}
    return h, v


def fix_tree(H, V, n):
    g = {(0, 0): ONE}
    for j in range(n):
        g[0, j+1] = mul(g[0, j], V[0, j])
    for j in range(n+1):
        for i in range(n):
            g[i+1, j] = mul(g[i, j], H[i, j])
    return (*gauge_links(H, V, g), g)


def edge(H, V, a, b):
    i, j = a
    di, dj = b[0]-i, b[1]-j
    if (di, dj) == (1, 0):
        return H[i, j]
    if (di, dj) == (-1, 0):
        return inv(H[i-1, j])
    if (di, dj) == (0, 1):
        return V[i, j]
    if (di, dj) == (0, -1):
        return inv(V[i, j-1])
    raise ValueError(f"Non-neighbor edge: {a}, {b}")


def transport(H, V, path):
    result = ONE
    for a, b in zip(path, path[1:]):
        result = mul(result, edge(H, V, a, b))
    return result


def boundary(n):
    return ([(i, 0) for i in range(n+1)] +
            [(n, j) for j in range(1, n+1)] +
            [(i, n) for i in range(n-1, -1, -1)] +
            [(0, j) for j in range(n-1, -1, -1)])


def random_path(n, rng, steps):
    p = [(n//2, n//2)]
    for _ in range(steps):
        i, j = p[-1]
        choices = [(a, b) for a, b in ((i+1, j), (i-1, j), (i, j+1), (i, j-1))
                   if 0 <= a <= n and 0 <= b <= n]
        p.append(rng.choice(choices))
    return p


def exact_quaternion(rng):
    v = [Fraction(rng.randint(-3, 3), 5) for _ in range(3)]
    s = sum(x*x for x in v)
    return ((1-s)/(1+s), *(2*x/(1+s) for x in v))


def exact_checks():
    rng = random.Random(90317)
    n = 2
    P = {(i, j): exact_quaternion(rng) for i in range(n) for j in range(n)}
    H, V = axial_links(P, n)
    g = {(i, j): exact_quaternion(rng) for i in range(n+1) for j in range(n+1)}
    g[0, 0] = ONE
    rawH, rawV = gauge_links(H, V, g)
    fixedH, fixedV, _ = fix_tree(rawH, rawV, n)
    checks = 0
    for q in list(P.values())+list(g.values()):
        assert mul(q, inv(q)) == ONE
        checks += 1
    for ij in H:
        assert fixedH[ij] == H[ij]
        checks += 1
    for ij in V:
        assert fixedV[ij] == V[ij]
        checks += 1
    for (i, j), p in P.items():
        assert plaquette(H, V, i, j) == p
        assert plaquette(rawH, rawV, i, j) == conjugate(g[i, j], p)
        checks += 2
    paths = [boundary(n)] + [random_path(n, rng, 12) for _ in range(12)]
    for p in paths:
        a = transport(H, V, p)
        b = transport(rawH, rawV, p)
        assert b == mul(mul(g[p[0]], a), inv(g[p[-1]]))
        checks += 1
    assert mul(P[0, 0], P[1, 0]) != mul(P[1, 0], P[0, 0])
    checks += 1
    return {"passed": checks, "arithmetic": "fractions.Fraction; exact noncommuting unit quaternions"}


def continuum_vertical(x, y, h, substeps):
    # Midpoint piecewise-constant ODE. Chronological product is on the right.
    result = ONE
    dt = h/substeps
    for k in range(substeps):
        result = mul(result, exp_pure(primitive(x, y+(k+0.5)*dt), dt))
    return result


def convergence_case(n, noisy, substeps=32):
    h = 1/n
    eps = h/5 if noisy else 0.0
    rng = random.Random(1700+n+int(noisy))
    P = {}
    plaquette_discrepancy = 0.0
    for i in range(n):
        for j in range(n):
            f = curvature(i*h, j*h)
            perturbed = (f[0]+0.6*eps, f[1], f[2]+0.8*eps)
            P[i, j] = exp_pure(perturbed, h*h)
            plaquette_discrepancy = max(plaquette_discrepancy,
                norm(sub(P[i, j], exp_pure(f, h*h))))
    assert plaquette_discrepancy <= h*h*eps+2e-14
    H, V = axial_links(P, n)
    g = {(i, j): exp_pure(tuple(rng.uniform(-3, 3) for _ in range(3)))
         for i in range(n+1) for j in range(n+1)}
    g[0, 0] = ONE
    rawH, rawV = gauge_links(H, V, g)
    fixedH, fixedV, fix = fix_tree(rawH, rawV, n)
    gauge_error = max([norm(sub(fixedH[k], H[k])) for k in H] +
                      [norm(sub(fixedV[k], V[k])) for k in V])
    assert gauge_error < 2e-10
    refV = {(i, j): continuum_vertical(i*h, j*h, h, substeps)
            for i in range(n+1) for j in range(n)}
    # M=L=1 are conservative analytic bounds for the chosen polynomial F.
    local_bound = h*eps+2*h*h
    ref_budget = h*h/(4*substeps)
    max_edge_error = max(norm(sub(V[k], refV[k])) for k in V)
    assert max_edge_error <= local_bound+ref_budget+2e-11
    paths = [boundary(n), [(0, 0), (0, 1), (0, 0)]]
    paths += [random_path(n, rng, 6*n) for _ in range(24)]
    max_ratio = 0.0
    path_errors = []
    for p in paths:
        actual, target = transport(H, V, p), transport(H, refV, p)
        error = norm(sub(actual, target))
        ny = sum(a[1] != b[1] for a, b in zip(p, p[1:]))
        bound = ny*local_bound
        budget = ny*ref_budget
        assert error <= bound+budget+2e-10
        raw = transport(rawH, rawV, p)
        expected_raw = mul(mul(g[p[0]], actual), inv(g[p[-1]]))
        assert norm(sub(raw, expected_raw)) < 2e-10
        if bound:
            max_ratio = max(max_ratio, error/bound)
        path_errors.append(error)
    # Deliberately reverse the strip order: ensure the test is nonabelian.
    wrong = ONE
    for i in range(n):
        wrong = mul(wrong, P[i, n//2])
    wrong_order_error = norm(sub(wrong, V[n, n//2]))
    assert wrong_order_error > 1e-10
    return {
        "n": n, "h": h, "epsilon": eps, "max_plaquette_discrepancy": plaquette_discrepancy,
        "gauge_reconstruction_error": gauge_error,
        "max_edge_error_vs_midpoint_reference": max_edge_error,
        "edge_analytic_bound": local_bound, "edge_reference_error_budget": ref_budget,
        "boundary_error_vs_midpoint_reference": path_errors[0],
        "boundary_analytic_bound": 2*(eps+2*h),
        "boundary_reference_error_budget": 2*n*ref_budget,
        "paths_checked": len(paths), "max_path_error_over_analytic_bound": max_ratio,
        "reversing_noncommutative_strip_order_error": wrong_order_error,
    }


def product_remainder_checks():
    rng = random.Random(4826)
    total = 0
    maximum_ratio = 0.0
    for count in (1, 2, 3, 8, 17):
        for step in (0.001, 0.03, 0.2):
            vectors = [tuple(rng.uniform(-1, 1) for _ in range(3)) for _ in range(count)]
            M = max(math.sqrt(sum(x*x for x in v)) for v in vectors)
            product = ONE
            linear = [1.0, 0.0, 0.0, 0.0]
            for v in vectors:
                product = mul(exp_pure(v, step), product)
                for j in range(3):
                    linear[j+1] += step*v[j]
            error = norm(sub(product, linear))
            bound = 0.5*(count*step*M)**2
            assert error <= bound+2e-13
            maximum_ratio = max(maximum_ratio, error/bound)
            total += 1
    return {"cases": total, "maximum_error_over_bound": maximum_ratio}


def sharp_noise_checks():
    rows = []
    for n in (4, 8, 16, 32, 64):
        h = 1/n
        p = exp_pure((1.0, 0.0, 0.0), h*h)
        P = {(i, j): p for i in range(n) for j in range(n)}
        H, V = axial_links(P, n)
        w = transport(H, V, boundary(n))
        target = exp_pure((1.0, 0.0, 0.0))
        assert norm(sub(w, target)) < 2e-11
        assert norm(sub(w, ONE)) > 0.95
        rows.append({"n": n, "plaquette_error": norm(sub(p, ONE)),
                     "plaquette_error_over_h_squared": norm(sub(p, ONE))/(h*h),
                     "boundary_error_from_flat": norm(sub(w, ONE))})
    return rows


def main():
    exact = exact_checks()
    remainders = product_remainder_checks()
    convergence = [convergence_case(n, noisy) for noisy in (False, True)
                   for n in (4, 8, 16, 32, 64)]
    sharp = sharp_noise_checks()
    for noisy in (False, True):
        rows = [r for r in convergence if (r["epsilon"] > 0) == noisy]
        for coarse, fine in zip(rows, rows[1:]):
            assert fine["boundary_error_vs_midpoint_reference"] < coarse["boundary_error_vs_midpoint_reference"]
    report = {
        "status": "PASS", "date": "2026-11-09", "group": "SU(2) as unit quaternions",
        "exact_checks": exact, "noncommutative_remainder_checks": remainders,
        "continuum_reference": {
            "method": "32 midpoint exponential substeps per vertical edge",
            "analytic_error_budget": "L*h^2/(4*substeps), L=1; floating-point rounding is not certified",
            "M": 1, "L_l1": 1,
        },
        "convergence": convergence, "coherent_O_h_squared_counterexample": sharp,
        "formalization_boundary": "See GAUGE_DISCRETE_CONTINUUM.md section 7; numerics are not proofs.",
    }
    destination = Path(__file__).resolve().parents[1]/"data"/"gauge_discrete_continuum_audit.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report, indent=2)+"\n")
    print(f"PASS: {exact['passed']} exact rational checks; {remainders['cases']} product-remainder cases")
    print("n   epsilon    boundary error    analytic bound")
    for row in convergence:
        print(f"{row['n']:2d}  {row['epsilon']:8.5f}   {row['boundary_error_vs_midpoint_reference']:.8f}       {row['boundary_analytic_bound']:.6f}")
    print(f"PASS: {sum(r['paths_checked'] for r in convergence)} path comparisons; 5 persistent-flux cases")
    print(destination)


if __name__ == "__main__":
    main()
