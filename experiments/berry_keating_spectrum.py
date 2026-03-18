#!/usr/bin/env python3
"""
THE NUMERICAL TEST: Does the parity-constrained Berry-Keating operator
reproduce the Riemann zeros?

The operator: H = -i(x d/dx + 1/2) on L²(0,∞)
This is the Weyl-symmetrized form of xp.

Deficiency indices are (1,1), giving a one-parameter family of
self-adjoint extensions parameterized by θ ∈ [0, 2π).

The eigenvalue equation: -i(x f'(x) + f(x)/2) = E f(x)
Solution: f(x) = C x^{iE - 1/2}

For f ∈ L²(0,∞), we need boundary conditions at x=0 and x=∞.
The boundary condition at x=0 is parameterized by θ:
  f(0+) ~ x^{iE-1/2} with the phase of the coefficient fixed by θ.

The spectrum for a given θ is determined by the condition that
f is normalizable (or satisfies the boundary condition at both ends).

On L²(0,∞) with NO boundary: f(x) = x^{iE-1/2} is not in L²
for any real E (it oscillates with constant amplitude |x^{-1/2}|).
So we need to regularize: work on [ε, L] with boundary conditions.

On [ε, L]: f(x) = x^{iE-1/2}
At x = ε: f(ε) = ε^{iE-1/2}
At x = L: f(L) = L^{iE-1/2}

Boundary condition (θ-parameterized):
f(L)/f(ε) = e^{iθ}  (periodic-like condition on the logarithmic coordinate)

In log coordinates u = ln(x), x ∈ [ε, L] → u ∈ [ln ε, ln L]:
f = e^{(iE-1/2)u}, so f is a plane wave in u.
The boundary condition f(ln L)/f(ln ε) = e^{iθ} gives:
e^{(iE-1/2)(ln L - ln ε)} = e^{iθ}
(iE - 1/2)(ln L - ln ε) = iθ + 2πin  for integer n

Let T = ln(L/ε). Then:
iE·T - T/2 = iθ + 2πin
E = (θ + 2πn)/T + i/(2T) ... wait, that gives complex E.

For REAL E (self-adjoint → real spectrum):
E·T = θ + 2πn  and  -T/2 = 0 (impossible for T ≠ 0)

Hmm, that means the operator on [ε,L] has NO real eigenvalues with
standard boundary conditions. The issue: the operator -i(x d/dx + 1/2)
is NOT essentially self-adjoint on L²(0,∞).

Let me reconsider. The standard approach (Berry-Keating, Sierra) uses
the HALF-LINE L²(0,∞) with a specific regularization at x=0.

The eigenvalue equation -i(xf' + f/2) = Ef gives f(x) = x^{iE-1/2}.
This is square-integrable near x=0 for Re(iE-1/2) > -1/2, i.e., always
(since |x^{iE-1/2}|² = x^{-1}, which diverges at 0). So we need a
DIFFERENT formulation.

SIERRA'S APPROACH: Use the Dirac equation in Rindler space with
delta-function potentials at positions x_n corresponding to squarefree
integers. The boundary condition at each potential encodes the
scattering phase, which is related to the Riemann zeta function.

THE SIMPLER TEST: Use the Riemann-Siegel theta function.
The completed zeta function ξ(s) = ξ(1-s) has zeros at ρ = 1/2 + iγ.
The Riemann-Siegel theta function θ(t) = arg(π^{-it/2} Γ(1/4 + it/2))
encodes the phase of ζ on the critical line.

The zeros of ζ(1/2+it) occur where Z(t) = e^{iθ(t)} ζ(1/2+it) changes
sign (Z is real-valued on the critical line by the functional equation).

The Berry-Keating conjecture in its simplest form: the eigenvalues of
a suitable quantization of H = xp are the γ_n (imaginary parts of zeros).

THE NUMERICAL APPROACH: Instead of constructing the operator,
let me test whether the SPACING STATISTICS of the Riemann zeros
match the predictions from the K·P = xp operator.

For the xp Hamiltonian, the semiclassical density of states is:
n(E) ~ (1/2π) ln(E/2π)  (Riemann-von Mangoldt formula)

The spacing distribution should follow GUE (Gaussian Unitary Ensemble)
statistics — the Montgomery-Odlyzko law.

But this is already well-known and doesn't test anything new.

WHAT ACTUALLY TESTS THE PARITY CONSTRAINT:
The parity-even condition on the source functional translates to:
the operator H must commute with the parity operator P: f(x) → f(1/x)/x.
This forces the boundary condition at x=0 and x=∞ to be related.

On L²(0,∞) with measure dx/x (which makes x → 1/x an isometry):
(Pf)(x) = f(1/x)
P² = id, so P has eigenvalues ±1.

H = -i(x d/dx + 1/2) satisfies PHP = -H (check: P maps x^{iE-1/2}
to x^{-iE-1/2}, so E → -E under parity). This means H ANTICOMMUTES
with P, so parity symmetry forces eigenvalues to come in ±E pairs.

The RIEMANN ZEROS DO come in conjugate pairs: if ρ = 1/2+iγ is a zero,
so is 1/2-iγ (equivalently, γ and -γ). This is the functional equation.

So parity of the source functional → H anticommutes with P → spectrum
symmetric about 0 → zeros come in ±γ pairs → functional equation.
This is CONSISTENT but doesn't prove the RH.

The stronger test: does parity-evenness PLUS some additional property
of the source functional (linearity, gauge invariance) force the
spectrum to be EXACTLY the Riemann zeros?

ACTUAL NUMERICAL COMPUTATION:
Let me compute the spectrum of xp on [ε, L] with the parity-symmetric
boundary condition f(L) = f(1/ε · L²) and check against zeros.

Actually, the cleanest test: on [1, N] with parity f(x) ↔ f(N/x),
the operator -i(x d/dx + 1/2) has discrete spectrum. Compute it
and compare with Riemann zeros scaled by ln(N)/(2π).
"""

import numpy as np
from scipy.linalg import eigh
from scipy.special import gamma as Gamma
import sys

# Known Riemann zeros (imaginary parts γ_n)
RIEMANN_ZEROS = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
]


def xp_operator_matrix(N_grid, x_min, x_max):
    """Discretize H = -i(x d/dx + 1/2) on [x_min, x_max]
    using a uniform grid in log-space (u = ln x).

    In u-coordinates: H = -i(d/du + 1/2)
    ... wait, let me redo this.

    x d/dx = d/du where u = ln x.
    So H = -i(d/du + 1/2) on [u_min, u_max] = [ln x_min, ln x_max].

    The measure dx/x = du makes this a standard operator on L²(du).

    Discretize d/du with centered differences on a uniform u-grid.
    """
    u_min = np.log(x_min)
    u_max = np.log(x_max)
    du = (u_max - u_min) / (N_grid + 1)
    u = np.linspace(u_min + du, u_max - du, N_grid)

    # Derivative matrix (centered differences, anti-Hermitian)
    D = np.zeros((N_grid, N_grid))
    for i in range(N_grid - 1):
        D[i, i+1] = 1.0 / (2 * du)
        D[i+1, i] = -1.0 / (2 * du)

    # H = -i(D + 1/2 I)
    # But -i(D + 1/2 I) is not Hermitian for generic boundary conditions.
    # The Hermitian (self-adjoint) version: H = (1/2)(-i D + (-i D)†) + (-i/2)I
    # Since D is anti-symmetric: D† = -D, so -iD is Hermitian.
    # H = -iD - i/2 I

    H = -1j * D - 1j * 0.5 * np.eye(N_grid)

    # Wait: H should be REAL (Hermitian with real eigenvalues).
    # Let me reconsider.
    # H = -i(d/du + 1/2) acting on L²(du).
    # On functions f(u): Hf = -if'(u) - i f(u)/2
    # This is: H = -i d/du - i/2

    # The operator -i d/du is the momentum operator, which is Hermitian
    # on L²(R) but on [a,b] needs boundary conditions.

    # With PERIODIC boundary conditions f(u_min) = f(u_max):
    # -i d/du has eigenvalues 2πn/(u_max - u_min) for n ∈ ℤ.
    # Then H = -id/du - i/2 has eigenvalues 2πn/T - i/2 where T = u_max - u_min.
    # These are COMPLEX, not real. So -i d/du - i/2 is NOT self-adjoint
    # with periodic BCs.

    # The issue: the +1/2 term makes this non-standard.
    # Let me use the DILATATION operator form instead.

    # On L²(R+, dx/x): the operator x d/dx is symmetric.
    # H_BK = -i(x d/dx) has eigenvalues γ on L²(R+, dx/x)
    # if ∫|x^{iγ}|² dx/x converges, which it doesn't.

    # THE RIGHT APPROACH: use a BOX on the positive half-line.
    # On [1, N] with Dirichlet BCs:
    # -i d/du on [0, ln N] with f(0) = f(ln N) = 0
    # Eigenvalues: E_n = nπ/ln(N) for n = 1, 2, ...
    # These are evenly spaced, NOT the Riemann zeros.

    # With ANTI-PERIODIC BCs (parity constraint):
    # f(ln N) = -f(0), eigenvalues: E_n = (n+1/2)π/ln(N)
    # Still evenly spaced.

    # The Riemann zeros are NOT evenly spaced.
    # The xp Hamiltonian on a box gives uniform spacing.
    # The NON-UNIFORM spacing (matching Riemann zeros) comes from
    # ADDITIONAL structure — the delta-function potentials in Sierra's
    # model, which encode the prime numbers.

    # CONCLUSION: The bare xp operator doesn't give Riemann zeros.
    # You need xp + prime potentials. The source functional would
    # need to encode the primes to give the right spectrum.

    return None


def test_bare_xp():
    """Test: does the bare xp operator (without prime potentials)
    give anything related to Riemann zeros?
    Answer: NO. The bare operator on a box gives uniform eigenvalues.
    """
    print("=" * 60)
    print("TEST: Bare xp operator on [1, N]")
    print("=" * 60)

    for N in [100, 1000, 10000]:
        T = np.log(N)
        # Eigenvalues of -i d/du on [0, T] with periodic BCs
        n_max = 20
        eigenvalues_periodic = np.array([2*np.pi*n/T for n in range(1, n_max+1)])
        eigenvalues_dirichlet = np.array([np.pi*n/T for n in range(1, n_max+1)])

        print(f"\nN = {N}, T = ln(N) = {T:.4f}")
        print(f"  Periodic eigenvalues (first 10): {eigenvalues_periodic[:10].round(4)}")
        print(f"  Riemann zeros (first 10):        {np.array(RIEMANN_ZEROS[:10]).round(4)}")
        print(f"  Ratio zeros/eigenvalues:         {(np.array(RIEMANN_ZEROS[:10]) / eigenvalues_periodic[:10]).round(4)}")

    print("\nCONCLUSION: Bare xp eigenvalues are uniformly spaced.")
    print("Riemann zeros are NOT uniformly spaced.")
    print("The bare operator DOES NOT reproduce the zeros.")
    print("Prime-number structure (potentials) is needed.")


def test_with_prime_potential():
    """Test Sierra's approach: xp with delta-function potentials
    at positions corresponding to squarefree integers.

    The scattering matrix for a delta potential at x_n encodes
    the local phase shift. The eigenvalue condition becomes:
    det(S(E)) = 0, where S is the product of scattering matrices.

    For the simplest version: a single delta potential at each
    prime p, with strength proportional to log(p).
    """
    print("\n" + "=" * 60)
    print("TEST: xp with prime potentials (simplified Sierra)")
    print("=" * 60)

    # The eigenvalue condition for xp + Σ V_n δ(x - p_n) on [1, N]:
    # In log coordinates: -i d/du + Σ V_n δ(u - ln p_n)
    # The transfer matrix across each delta:
    # T_n = [[1, -iV_n], [0, 1]] in the (f, f') basis
    # Eigenvalue condition: product of transfer matrices gives
    # a specific phase.

    # Actually, let me compute the more standard version:
    # The spectral determinant: Π_p (1 - p^{-1/2-iE}) = ζ(1/2+iE)
    # The zeros of ζ(1/2+iE) are at E = γ_n (the Riemann zeros).

    # So the "spectral" test is: compute ζ(1/2+iE) and find its zeros.
    # This is circular — we'd be computing Riemann zeros to check
    # against Riemann zeros. Not a test of the operator.

    # THE REAL QUESTION: Does the SOURCE FUNCTIONAL encode the primes?
    # In the framework: φ = trace (for gravity). What makes φ = log
    # (the "prime source functional") special?

    # The connection: the Euler product ζ(s) = Π_p (1-p^{-s})^{-1}
    # writes ζ as a product over primes. Each factor (1-p^{-s})^{-1}
    # = Σ_k p^{-ks} = Σ_k e^{-ks log p}. With source value φ_p = log p
    # and Boltzmann weight e^{-βφ_p}, the partition function is exactly
    # the Euler product!

    # Z(β) = Π_p Σ_k e^{-k β log p} = Π_p 1/(1 - p^{-β}) = ζ(β)

    print("\nThe Euler product: ζ(s) = Π_p (1 - p^{-s})^{-1}")
    print("With source functional φ_p = log(p):")
    print("  Z(β) = Π_p Σ_k e^{-kβ log p} = Π_p 1/(1-p^{-β}) = ζ(β)")
    print()
    print("The partition function IS the Riemann zeta function!")
    print("The K-sector projection (Wick rotation k → -iβ) of the")
    print("quantum amplitude sum gives ζ(β) as a PARTITION FUNCTION.")
    print()
    print("This means: ζ(s) = Tr(e^{-sH}) where H is the 'prime")
    print("Hamiltonian' with eigenvalues log(n) for all positive")
    print("integers n (the Primon gas).")
    print()
    print("The ZEROS of ζ correspond to the RESONANCES of H — values")
    print("of s where the trace has a pole/zero in the analytic")
    print("continuation.")
    print()
    print("The K/P framework adds: the Born rule |z|² and the")
    print("Berry-Keating Hamiltonian K·P are the two canonical")
    print("quadratics on the SAME K/P space. The partition function")
    print("ζ(s) = Tr(e^{-sH}) is the K-sector projection of the")
    print("quantum amplitude sum Σ e^{ikφ_n} = Σ n^{ik}.")


def main():
    test_bare_xp()
    test_with_prime_potential()

    print("\n" + "=" * 60)
    print("FINAL ASSESSMENT")
    print("=" * 60)
    print()
    print("1. The bare xp operator gives uniform eigenvalues, NOT")
    print("   the Riemann zeros. Prime structure is needed.")
    print()
    print("2. The partition function Z(β) = Π_p 1/(1-p^{-β}) = ζ(β)")
    print("   IS the Riemann zeta function, with φ_p = log(p).")
    print()
    print("3. The source functional's parity-evenness forces the")
    print("   functional equation ξ(s) = ξ(1-s) (proven in StrongCP.lean")
    print("   as K/P parity orthogonality).")
    print()
    print("4. The self-adjoint extension question (Sierra's tuning")
    print("   problem) requires encoding the prime structure into the")
    print("   operator's domain. The source functional alone (being")
    print("   linear and universal) cannot select the primes.")
    print()
    print("5. WHAT THE FRAMEWORK CONTRIBUTES:")
    print("   - K·P = xp is uniquely boost-invariant (PROVEN)")
    print("   - ζ(s) is the K-sector partition function (structural)")
    print("   - Parity → functional equation (consistent)")
    print("   - The self-adjoint extension is NOT fixed by the source")
    print("     functional alone — it needs prime-specific input")
    print()
    print("VERDICT: The framework provides a structural HOME for the")
    print("Berry-Keating Hamiltonian but does NOT solve the RH.")
    print("The missing ingredient: why the primes? The source functional")
    print("is universal (works for any energy spectrum), while the")
    print("Riemann zeros require the SPECIFIC spectrum log(n).")


if __name__ == "__main__":
    main()
