"""Two-generation entanglement of the pi/4 law (Hopf S^7->S^4 / two-qubit check).
A = first-generation child class, B = second-step label (grandchild class, or action gap).
Run from repo root. Reuses binormalized_phase_diagram.py engine (defs only)."""
import math, numpy as np, collections
src = open("binormalized_phase_diagram.py").read().split("\nPHIS =")[0]
g = {"__name__": "engine"}; exec(compile(src, "engine", "exec"), g)
children, feasible_born, root, levels = g["children"], g["feasible_born"], g["root"], g["levels"]
P4 = math.pi / 4

def law(p):
    ok, (cls, rho) = feasible_born(p, P4, want_point=True)
    assert ok
    out = [(ck, mu, gg, r * np.exp(1j * gg * P4)) for (ck, mu, gg), r in zip(cls, rho)]
    coh = sum(mu * a for _, mu, _, a in out); born = sum(mu * abs(a)**2 for _, mu, _, a in out)
    assert abs(coh - 1) < 1e-6 and abs(born - 1) < 1e-6, (coh, born)
    return out

def name(key):
    n, rel = levels[key[0]][key] if key in levels[key[0]] else (key[0], None)
    return f"n{n}:{rel}"

def report(psi, rowlab, collab, title):
    psi = np.array(psi, complex)
    nrm = np.linalg.norm(psi); psi = psi / nrm
    sv = np.linalg.svd(psi, compute_uv=False); p = sv**2; p = p[p > 1e-15]
    S = float(-(p * np.log2(p)).sum())
    rA = psi @ psi.conj().T
    C = math.sqrt(max(0.0, 2 * (1 - np.trace(rA @ rA).real)))
    shared = [j for j in range(psi.shape[1]) if all(abs(psi[i, j]) > 1e-12 for i in range(psi.shape[0]))]
    pa = np.sum(abs(psi)**2, axis=1)
    HA = float(-(pa[pa > 0] * np.log2(pa[pa > 0])).sum())
    print(f"\n--- {title} --- (norm before renorm {nrm:.6f})")
    print("  columns:", collab)
    for i, r in enumerate(psi):
        print(f"  {rowlab[i]:>14s}: " + "  ".join(f"{z.real:+.4f}{z.imag:+.4f}i" for z in r))
    print(f"  Schmidt probs {np.round(p, 6)}  entropy S = {S:.6f} bits | concurrence C = {C:.6f}")
    print(f"  first-gen Born entropy H(A) = {HA:.6f}  (block-diagonal/record value would be S = H(A))")
    print(f"  shared columns (reached from every row): {len(shared)}/{psi.shape[1]}")
    if psi.shape == (2, 2):
        a, b, c, d = psi.ravel()
        print(f"  2x2: C = 2|ad - bc| = {2*abs(a*d - b*c):.6f}")
    return S, C

# generation 1
g1 = law(root)
print("root children:", [(name(ck), mu, gg, np.round(a, 4)) for ck, mu, gg, a in g1])
rows = [name(ck) for ck, *_ in g1]
# generation 2, labeled paths aggregated per (child, grandchild class) and per (child, gap)
byclass = collections.defaultdict(complex); bygap = collections.defaultdict(complex)
bygap_born = collections.defaultdict(float)
for i, (c, mu1, g1gap, a1) in enumerate(g1):
    for gc, mu2, g2gap, a2 in law(c):
        amp = math.sqrt(mu1 * mu2) * a1 * a2
        byclass[(i, gc)] += amp
        bygap[(i, g2gap)] += amp      # coherent sum over classes sharing a gap
    print(f"  {name(c)} -> ", [(name(gc), mu2, gg, np.round(a2, 4)) for gc, mu2, gg, a2 in law(c)])
gcs = sorted({k[1] for k in byclass}); gaps = sorted({k[1] for k in bygap})
M1 = [[byclass.get((i, gc), 0) for gc in gcs] for i in range(len(g1))]
M2 = [[bygap.get((i, gp), 0) for gp in gaps] for i in range(len(g1))]
report(M1, rows, [name(x) for x in gcs], "B = grandchild CLASS (paths into the same causet can interfere)")
report(M2, rows, gaps, "B = second-step ACTION GAP (classes with equal gap summed coherently)")
# interference view: Q (coherent, class-identified) vs P (Born) on grandchild classes
print("\n--- interference on shared grandchildren ---")
for j, gc in enumerate(gcs):
    col = [M1[i][j] for i in range(len(g1))]
    Q = abs(sum(col))**2; P = sum(abs(z)**2 for z in col)
    print(f"  {name(gc):>40s}: P = {P:.4f}  Q = {Q:.4f}  (Q-P = {Q-P:+.4f})")
