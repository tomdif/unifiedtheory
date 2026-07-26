"""Single-plaquette adjoint running determinant det(1 - Ad_W)|_roots = prod_{i!=j}(1 - lam_i/lam_j).
Shows the connection-DEPENDENCE (running) of the adjoint fermion measure for the
weak triplet SU(2) and color octet SU(3). The Cartan directions (eigenvalue 1) are
the massless modes and are excluded (that is the |_roots restriction)."""
import numpy as np

def run_det_roots(lams):
    lams = np.asarray(lams, dtype=complex)
    n = len(lams)
    p = 1.0 + 0j
    for i in range(n):
        for j in range(n):
            if i != j:
                p *= (1 - lams[i] / lams[j])
    return p

print("=== SU(2) weak triplet: W = diag(a, 1/a) ===")
for a in [1.0, 2.0, 0.5, 3.0]:
    d = run_det_roots([a, 1/a])
    print(f"  a={a:>4}:  det(1-Ad_W)|_roots = {d.real:+.4f}  (nonconstant => runs)")

print("=== SU(3) color octet: W = diag(l1,l2,l3), l1*l2*l3=1 ===")
import cmath
def su3(t1, t2):  # two angles, unit determinant
    l = [cmath.exp(1j*t1), cmath.exp(1j*t2), cmath.exp(-1j*(t1+t2))]
    return l
for (t1,t2,name) in [(0.0,0.0,"trivial"),(0.7,0.3,"generic A"),(1.2,-0.4,"generic B"),(np.pi,0.0,"center-ish")]:
    l = su3(t1,t2)
    d = run_det_roots(l)
    print(f"  {name:>10}: det|_roots = {d.real:+.4f} {d.imag:+.4f}i  (real, nonconstant => runs)")

print("\nVERDICT: |_roots determinant is connection-dependent (nonconstant) for both")
print("triplet and octet -> the adjoint fermion measure RUNS (does not decouple).")
print("Cartan eigenvalue-1 directions excluded = the massless modes (AdjointMasslessMeasure).")
print("Sign/magnitude of the beta-coefficient needs the Grassmann determinant power + R3.")
