"""
TEST A: Falsification test of V_us = 1/sqrt(20) prediction.
Enumerate depth-2 algebraic combinations of the 11 atoms and count menu-matches
to PDG V_us = 0.2243 within 1% (or V_us^2 = 0.05031 within 2%).
"""

from fractions import Fraction
from math import sqrt, isfinite
import itertools

# ---- 11 atoms ----------------------------------------------------------------
sqrt7 = sqrt(7)

# (label, exact_value_or_None, float_value)
ATOMS = [
    ("C_int",        Fraction(3, 20),                    3/20),
    ("a1",           Fraction(1, 3),                     1/3),
    ("lambda_star",  Fraction(3, 5),                     3/5),
    ("ls_minus_a1",  Fraction(4, 15),                    4/15),
    ("b1",           Fraction(1, 5),                     1/5),
    ("b1_sq",        Fraction(1, 25),                    1/25),
    ("b2_sq",        Fraction(1, 50),                    1/50),
    ("r1",           Fraction(1, 3),                     1/3),
    ("r2",           None,                                1/3 + sqrt7/21),
    ("r3",           None,                                1/3 - sqrt7/21),
    ("r2_r3",        Fraction(2, 21),                    2/21),
]
# Note: eigenvalues 3/5, (5±√7)/30 — 3/5 already present as lambda_star.
# Add the two irrational eigenvalues for completeness.
ATOMS += [
    ("eig_plus",     None, (5 + sqrt7) / 30),
    ("eig_minus",    None, (5 - sqrt7) / 30),
]

# ---- PDG targets -------------------------------------------------------------
PDG_VUS  = 0.2243
PDG_TOL  = 0.01      # 1%
PDG_VUS2 = 0.05031
PDG_TOL2 = 0.02      # 2%

VUS_LO,  VUS_HI  = PDG_VUS  * (1 - PDG_TOL),  PDG_VUS  * (1 + PDG_TOL)
VUS2_LO, VUS2_HI = PDG_VUS2 * (1 - PDG_TOL2), PDG_VUS2 * (1 + PDG_TOL2)

VALUE_LO, VALUE_HI = 0.001, 10.0

# ---- Helper: safe ops --------------------------------------------------------
def safe_add(a, b):  return a + b
def safe_sub(a, b):  return a - b
def safe_mul(a, b):  return a * b
def safe_div(a, b):
    if abs(b) < 1e-15: return None
    return a / b
def safe_sqrt(x):
    if x is None or x <= 0: return None
    return sqrt(x)
def safe_sq(x):
    if x is None: return None
    return x * x
def safe_inv(x):
    if x is None or abs(x) < 1e-15: return None
    return 1.0 / x

BIN_OPS = [
    ("+", safe_add),
    ("-", safe_sub),
    ("*", safe_mul),
    ("/", safe_div),
]

# ---- Build depth-1 expressions: atom alone, atom^2, sqrt(atom), 1/atom ------
def depth1_exprs():
    out = []
    for name, _exact, val in ATOMS:
        out.append((name, val))
        out.append((f"({name})^2", safe_sq(val)))
        sq = safe_sqrt(val)
        if sq is not None:
            out.append((f"sqrt({name})", sq))
        inv = safe_inv(val)
        if inv is not None:
            out.append((f"1/({name})", inv))
    # Filter
    return [(n, v) for n, v in out if v is not None and isfinite(v)]

# ---- Build depth-2 expressions: binop on two atoms, plus sqrt/sq/inv of those
def depth2_exprs(d1):
    """Depth-2: take two atoms, combine with binop. Then optionally apply
    sqrt/sq/inv to the result. Also include depth-1 results."""
    out = list(d1)  # depth-1 already includes single-atom ops
    n_atoms = len(ATOMS)
    # Pairs (a, b) from raw atoms (not depth-1 already-modified)
    raw = [(name, val) for name, _, val in ATOMS]
    for i, j in itertools.product(range(n_atoms), repeat=2):
        ai_name, ai_val = raw[i]
        aj_name, aj_val = raw[j]
        for op_name, op_fn in BIN_OPS:
            v = op_fn(ai_val, aj_val)
            if v is None or not isfinite(v):
                continue
            expr = f"({ai_name} {op_name} {aj_name})"
            out.append((expr, v))
            # Single application of sqrt
            sq = safe_sqrt(v)
            if sq is not None:
                out.append((f"sqrt{expr}", sq))
            # Single application of squaring
            out.append((f"{expr}^2", v * v))
            # Single application of inverse
            inv = safe_inv(v)
            if inv is not None:
                out.append((f"1/{expr}", inv))
    return [(n, v) for n, v in out if v is not None and isfinite(v) and VALUE_LO <= abs(v) <= VALUE_HI]

# ---- Run the enumeration -----------------------------------------------------
d1 = depth1_exprs()
all_exprs = depth2_exprs(d1)
print(f"Total depth-≤2 expressions enumerated (after value-range filter): {len(all_exprs)}")

# ---- Filter for V_us matches (1%) -------------------------------------------
vus_matches = []
for expr, v in all_exprs:
    if VUS_LO <= v <= VUS_HI:
        delta = (v - PDG_VUS) / PDG_VUS * 100  # percent
        vus_matches.append((expr, v, delta))

# ---- Filter for V_us^2 matches (2%) -----------------------------------------
vus2_matches = []
for expr, v in all_exprs:
    if VUS2_LO <= v <= VUS2_HI:
        delta = (v - PDG_VUS2) / PDG_VUS2 * 100
        vus2_matches.append((expr, v, delta))

# ---- Deduplicate by value (keep shortest expression per value bucket) -------
def dedup_by_value(matches, tol=1e-6):
    """Group by value within tol; keep one representative per group + count."""
    buckets = []
    for expr, v, d in sorted(matches, key=lambda x: (len(x[0]), abs(x[2]))):
        placed = False
        for bucket in buckets:
            if abs(v - bucket['v']) < tol:
                bucket['exprs'].append(expr)
                placed = True
                break
        if not placed:
            buckets.append({'v': v, 'd': d, 'exprs': [expr]})
    out = []
    for b in buckets:
        out.append((b['exprs'][0], b['v'], b['d'], len(b['exprs']), b['exprs']))
    return out

vus_matches_dedup  = dedup_by_value(vus_matches)
vus2_matches_dedup = dedup_by_value(vus2_matches)

print()
print("=" * 78)
print(f"V_us MATCHES (within 1% of PDG V_us = {PDG_VUS}): "
      f"{len(vus_matches)} raw, {len(vus_matches_dedup)} unique values")
print("=" * 78)
for expr, v, d, k, all_exprs_for_v in sorted(vus_matches_dedup, key=lambda x: abs(x[2]))[:15]:
    print(f"  {v:.6f}  Δ={d:+6.3f}%   ({k} aliases)  e.g. {expr}")
    for e in all_exprs_for_v[:5]:
        print(f"        - {e}")
    if k > 5:
        print(f"        ... +{k-5} more")

print()
print("=" * 78)
print(f"V_us^2 MATCHES (within 2% of PDG V_us^2 = {PDG_VUS2}): "
      f"{len(vus2_matches)} raw, {len(vus2_matches_dedup)} unique values")
print("=" * 78)
for expr, v, d, k, all_exprs_for_v in sorted(vus2_matches_dedup, key=lambda x: abs(x[2]))[:15]:
    print(f"  {v:.6f}  Δ={d:+6.3f}%   ({k} aliases)  e.g. {expr}")
    for e in all_exprs_for_v[:5]:
        print(f"        - {e}")
    if k > 5:
        print(f"        ... +{k-5} more")

# ---- Top 5 closest to PDG ----------------------------------------------------
print()
print("=" * 78)
print("TOP 5 CLOSEST V_us MATCHES (unique values)")
print("=" * 78)
top5_vus = sorted(vus_matches_dedup, key=lambda x: abs(x[2]))[:5]
print(f"{'rank':<5}{'value':<12}{'Δ %':<10}{'#aliases':<10}{'shortest expr':<40}")
for k, (expr, v, d, n, _) in enumerate(top5_vus, 1):
    print(f"{k:<5}{v:<12.6f}{d:<+10.3f}{n:<10}{expr:<40}")

print()
print("=" * 78)
print("TOP 5 CLOSEST V_us^2 MATCHES (unique values)")
print("=" * 78)
top5_vus2 = sorted(vus2_matches_dedup, key=lambda x: abs(x[2]))[:5]
print(f"{'rank':<5}{'value':<12}{'Δ %':<10}{'#aliases':<10}{'shortest expr':<40}")
for k, (expr, v, d, n, _) in enumerate(top5_vus2, 1):
    print(f"{k:<5}{v:<12.6f}{d:<+10.3f}{n:<10}{expr:<40}")

# ---- The framework's prediction itself -------------------------------------
print()
print("=" * 78)
print("FRAMEWORK PREDICTION (sqrt(C_int*a1) = 1/sqrt(20))")
print("=" * 78)
fw_vus = sqrt(3/20 * 1/3)
fw_vus2 = 1/20
print(f"  V_us  predicted: {fw_vus:.6f}, PDG = {PDG_VUS}, Δ = {(fw_vus-PDG_VUS)/PDG_VUS*100:+.3f}%")
print(f"  V_us^2 predicted: {fw_vus2:.6f}, PDG = {PDG_VUS2}, Δ = {(fw_vus2-PDG_VUS2)/PDG_VUS2*100:+.3f}%")
