"""k-child check for the Hopf/Berry reading of the pi/4 law.
Reuses the engine of binormalized_phase_diagram.py (definitions only, lines < PHIS)."""
import math, sys, collections, numpy as np
from scipy.optimize import brentq
src = open("binormalized_phase_diagram.py").read().split("\nPHIS =")[0]
g = {"__name__": "engine"}; exec(compile(src, "engine", "exec"), g)
parents, children, feasible_born, nelem = g["parents"], g["children"], g["feasible_born"], g["nelem"]
root = g["root"]
P4 = math.pi / 4

def binary_pins(mu1, g1, mu2, g2):
    """phi in (0,pi) solving x1 e^{i g1 phi}+x2 e^{i g2 phi}=1, x>=0, x1^2/mu1+x2^2/mu2=1 (x=mu*rho)."""
    def xs(phi):
        d = math.sin((g2 - g1) * phi)
        if abs(d) < 1e-12: return None
        return math.sin(g2 * phi) / d, -math.sin(g1 * phi) / d
    def h(phi):
        x = xs(phi);  return None if x is None else x[0]**2/mu1 + x[1]**2/mu2 - 1
    grid = np.linspace(1e-4, math.pi - 1e-4, 200001); roots = []
    vals = [h(p) for p in grid]
    for i in range(len(grid) - 1):
        a, b = vals[i], vals[i+1]
        if a is None or b is None or not np.isfinite(a) or not np.isfinite(b): continue
        if abs(a) > 50 or abs(b) > 50: continue          # skip poles
        if a == 0 or a * b < 0:
            r = brentq(h, grid[i], grid[i+1]) if a*b < 0 else grid[i]
            x = xs(r)
            if x and min(x) >= -1e-9: roots.append(round(r, 9))
    return sorted(set(roots))

stats = collections.Counter(); binary = []; twogap = []
for p in parents:
    cls = [(mu, gg) for ck, (mu, gg) in children[p].items()]
    K = len(cls); M = sum(mu for mu, _ in cls); stats[K] += 1
    if K == 2:
        (m1, g1), (m2, g2) = cls
        pins = binary_pins(m1, g1, m2, g2)
        binary.append((p, nelem(p), (m1, g1), (m2, g2), pins))
    gaps = sorted(set(gg for _, gg in cls))
    if gaps == [-1, 1]:
        mp = sum(mu for mu, gg in cls if gg == 1); mm = sum(mu for mu, gg in cls if gg == -1)
        twogap.append((p, K, mp, mm))
print("parents by number of child classes K:", dict(sorted(stats.items())))
print(f"\n=== K=2 (qubit) parents: {len(binary)}  -- pinned phases in (0,pi) ===")
pat = collections.defaultdict(list)
for p, n, c1, c2, pins in binary:
    pat[(tuple(sorted([c1, c2])), tuple(round(x/math.pi, 6) for x in pins))].append(n)
has_pi4 = sum(1 for *_, pins in binary if any(abs(x - P4) < 1e-6 for x in pins))
for (cc, pins), ns in sorted(pat.items(), key=lambda t: -len(t[1])):
    print(f"  (mu,gap) {cc}: pinned phi/pi = {list(pins)}   count {len(ns)} (n={sorted(set(ns))})")
print(f"  binary parents whose pinned set CONTAINS pi/4: {has_pi4}/{len(binary)}")
print(f"\n=== parents with gaps exactly {{+1,-1}}: {len(twogap)}; formula cos^2 phi=(1/mu+ + 1/mu-)/4 ===")
for p, K, mp, mm in twogap[:20]:
    c2 = (1/mp + 1/mm)/4; phi = math.acos(math.sqrt(c2)) if c2 <= 1 else float('nan')
    ok, _ = feasible_born(p, phi)
    print(f"  K={K} mu+={mp} mu-={mm}: phi = {phi/math.pi:.6f} pi  feasible-check={ok}  (root={p==root})")
# K>=3: feasible phi windows on a grid (open sets, grid-visible)
print("\n=== K>=3 parents: feasible-phi fraction on (0,pi/2] grid and pi/4 membership ===")
grid = np.linspace(math.pi/2/200, math.pi/2, 200)
fr = collections.defaultdict(list); contains = collections.Counter(); tot = collections.Counter()
for p in parents:
    K = len(children[p])
    if K < 3: continue
    f = sum(feasible_born(p, phi)[0] for phi in grid) / len(grid)
    fr[K].append(f); tot[K] += 1; contains[K] += feasible_born(p, P4)[0]
for K in sorted(fr):
    a = np.array(fr[K])
    print(f"  K={K}: n={tot[K]:4d}  feasible fraction mean {a.mean():.3f} min {a.min():.3f}  | pi/4 feasible {contains[K]}/{tot[K]}")
