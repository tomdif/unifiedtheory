# Local mediators: the required energy is not enough to produce a graviton

Date: 2026-09-11

A local electric field subject to a Gauss constraint can supply the
positive inverse Laplacian missing from the compact tensor wave
Hamiltonian. That static construction is exact. It does not complete
the proposed mechanism: the natural two sets of tensor-current Gauss
constraints fail to commute. Correct constraint reduction changes the
canonical brackets. In a minimal exact example, the apparent linear
oscillator disappears and the original tensor variables are constant.

Ordinary stable auxiliary oscillators have a separate obstruction:
when the original tensor pairs remain a canonical principal subspace
with their previous quadratic block, at least two frequencies stay
O(|k|³), even with gapless auxiliaries and arbitrary stable mixing.
Neither result excludes a different interacting spin phase or a
different joint constraint system. The latter is the constructive
target identified here. Einstein gravity and the TOE remain unproved.

## 1. The specific missing term

The regular unwrapped expansion of
[the compact tensor dynamics](COMPACT_TENSOR_DYNAMICS.md) has two
nonzero-momentum tensor pairs with

    H0 = (J/2) |v|² |P|² + (g/2) |v|⁴ |Q|²,
    v_i = 2 sin(k_i/2),       omega0 = sqrt(J g) |v|³,
    J,g > 0.                                               (1)

The same note identifies the formal linear-wave diagnostic

    Hdiag = (J/2) <C0 pi, L^(-1) C0 pi>
            + (g/2) <R h, L^(-1) R h>,                    (2)

where L is the positive lattice Laplacian on nonzero momentum,
C0 is the curl of trace-adjusted momentum, and R is double curl.
On tensor representatives, C0* C0 = |v|² I and
R* R = |v|⁴ I. Equation (2) would give omega = sqrt(Jg)|v|
if the original tensor canonical brackets were retained.

These are continuum-symbol statements about a chosen expansion.
They do not prove that the fixed five-state spin model realizes a
gapless phase. The distinction between cubic local tensor dynamics
and the linearized-gravity target also appears in
[Gu and Wen](https://arxiv.org/html/0907.1203); that paper explicitly
leaves reliability questions for its proposed linear model.

## 2. Unconstrained stable mediators cannot add the positive stiffness

For a positive quadratic Hamiltonian, divide variables into the
original canonical pairs x and independent auxiliary pairs y:

    H = (1/2) x^T A x + x^T B y + (1/2) y^T D y,
    K = [[A,B],[B^T,D]] > 0.                               (3)

Minimizing over y, or performing its static Gaussian integral, gives

    Aeff = A - B D^(-1) B^T,
    0 < Aeff <= A.                                         (4)

It lowers the static energy. A positive inverse-Laplacian addition
larger than the original infrared stiffness cannot follow from this
elimination while A remains fixed. For example, a massless coordinate
y with potential

    (1/2) g k⁴ q² + lambda k² q y + (1/2) c² k² y²

has determinant k⁴(g c² k² - lambda²). At nonzero fixed lambda
it becomes unstable at sufficiently small k. A compensating bare
q² term is a change of the original block, not a generated positive
term in (4).

Frequency dependence might seem to evade a static calculation.
The following result checks the full coupled spectrum instead.

## 3. At least two slow frequencies survive stable canonical mixing

Let Omega be the canonical symplectic matrix, with one block
[[0,1],[-1,0]] per pair. For K > 0 let
d1(K) <= ... <= dn(K) be its positive oscillator frequencies.
If A is its restriction to m complete canonical pairs, then

    dj(K) <= dj(A),       j = 1,...,m.                      (5)

This is the lower side of symplectic interlacing. The relevant
matrix framework is given by
[Bhatia and Jain](https://arxiv.org/pdf/1803.04647).
Here is a short proof using Hermitian inertia.

A Williamson symplectic change of basis makes K diagonal with each
frequency repeated on its conjugate pair. The Hermitian matrix
K - i t Omega then has, by congruence, one pair of signs determined
by dj(K)-t and dj(K)+t. Its negative index equals the number of
frequencies strictly below t. Restricting to the original canonical
subspace cannot increase that negative index. For t > dj(A), the
restricted matrix has at least j negative directions, so the full
matrix has at least j. Taking t down to dj(A) proves (5).

Apply (5) with m = 2 and A equal to the block in (1). For every
nonzero momentum at which the complete quadratic Hamiltonian is
positive,

    d1(K), d2(K) <= sqrt(Jg) |v|³.                         (6)

The same conclusion holds if A has finite regular blocks
A_PP = O(|k|²), A_QQ = O(|k|⁴), A_PQ = O(|k|³).
The canonical rescaling Q = |k|^(-1/2) Q',
P = |k|^(1/2) P' makes every block O(|k|³), which bounds
its frequencies by that order.

No auxiliary gap or analytic inverse D is needed in (5). A new
linear branch can appear, but at least two slower branches remain.
The theorem does not identify their overlaps with a particular
observable; it bounds the complete spectrum.

The hypotheses matter. This argument does not cover a new constraint
that removes or changes the original canonical subspace, a changed
original stiffness of lower derivative order, or a non-Gaussian phase
where the assumed quadratic description fails. Positive definiteness
is imposed after removal of any already-established gauge directions.
This is not a theorem about every finite-spin Hamiltonian.

## 4. A Gauss constraint does supply the positive inverse Laplacian

Let D be the discrete divergence from links to vertices on a connected
periodic lattice, and let L = D D^T. For a zero-mean source rho,
consider the positive local energy subject to an exact constraint:

    minimize (1/2) E^T E,       subject to D E = rho.

On the zero-mean subspace,

    E_* = D^T L^(-1) rho,
    min energy = (1/2) rho^T L^(-1) rho.                   (7)

Indeed, every solution is E_* + E_T with D E_T = 0.
The cross term vanishes, giving the minimum plus ||E_T||²/2.
The inverse excludes the constant mode; a nonzero total charge
requires different boundary conditions or compensating charge.

Unlike (4), the trial E = 0 is inadmissible at nonzero source.
Thus (7) supplies a positive inverse Laplacian without a negative
auxiliary quadratic energy. It is the elementary Coulomb mechanism.

Taking independent electric fields with sources C0 pi and R h
would reproduce (2) as a static minimum. But when those sources are
dynamical and conjugate, their constraints must be tested together.

## 5. The two tensor-current Gauss laws are not first class

Give each electric field its own canonical potential. The two
electric sets E and F commute with each other and with h,pi.
The proposed constraints are

    G_P = D E - C0 pi,
    G_Q = D F - R h.                                      (8)

With {h_i,pi_j} = delta_ij their cross bracket is

    {G_P,G_Q} = -C0 R^T.                                  (9)

It does not vanish. In the continuum real-coefficient convention,
let X(k) be the cross-product matrix and use a Frobenius tensor basis:

    C0(pi) = X(k) [pi - (tr pi) I/2],
    R(h)   = X(k) h X(k)^T.

At k != 0 the product C0 R^T has rank two. For k along z,
R retains the transverse symmetric block, and C0 kills its trace
while acting invertibly on its two tracefree components. Rotations
give the same rank for every nonzero real k. Fourier sine/cosine
partners restore the factors of i in the real-space derivative
convention; they do not remove the nonzero pairing.

The 18 proposed constraints, nine of each kind, therefore have a
bracket matrix of rank four in this momentum-block convention.
Their incompatible part is precisely in the tensor channels that
were meant to propagate. This is also visible without a continuum
limit: the exact finite-lattice C,R rows in the
[compact audit](data/compact_tensor_dynamics_audit.json) include a pair
whose integer contraction is nonzero modulo five.

The original four linear tensor constraints commute with (8),
because C0 B^T = 0 and R G = 0. That does not fix the cross bracket
between the new constraints themselves. Independent electric
auxiliaries contribute no opposite term to cancel (9).

These are not two compatible sets of gauge generators. Their
nonzero bracket is a constant operator, not a combination vanishing
on the constraint surface. In canonical quantization, a pair with
nonzero scalar commutator cannot both annihilate a nonzero physical
state. One must change the constraint system or carry out a
second-class reduction with the corresponding new brackets.

## 6. Exact reduction removes the apparent oscillator

A single tensor channel already displays the problem. At k > 0
take three canonical pairs (q,p), (a,e), (b,f), and set

    H = (J/2)e² + (g/2)f²,
    c1 = k(e-p) = 0,
    c2 = k f - k² q = 0.                                 (10)

This is the one-mode version of the two longitudinal electric
minimizations. Substitution gives

    H|_c = (J/2)p² + (g/2)k² q².                          (11)

Keeping {q,p}=1 would suggest omega = sqrt(Jg)k.
However,

    {c1,c2} = -k³,
    {q,p}_Dirac = 0.                                     (12)

There is an especially transparent derivation. Pull back the full
canonical one-form to e = p, f = kq:

    p dq + e da + f db = p d(q+a) + kq db.

The reduced canonical pairs are consequently

    (Q1,P1) = (q+a,p),       (Q2,P2) = (b,kq).

The actual reduced Hamiltonian is

    Hred = (J/2) P1² + (g/2) P2².                         (13)

There are two free pairs, not one oscillator. Both original q and p
are conserved; the auxiliary combinations drift. The exact
Hamiltonian-flow matrix is nonzero but its square is zero, so all
its eigenvalues vanish. Static substitution got the energy right
and the symplectic structure wrong.

This example is a counterexample to the proposed inference from
(7) to a physical wave. It is not a classification of all possible
constrained mediators. Additional terms acting on a,b change its
dynamics and require a fresh mode and constraint analysis.
Likewise, minimizing transverse electric energy does not remove
the corresponding canonical potentials from a quantum theory.

## 7. Revised construction target

The preceding
[convex matter bound](CONVEX_MATTER_POLE_BOUND.md) prevented a
fixed-residue graviton identification with the chosen matter
bilinears. The present calculation addresses a different route:
supplying the missing response through auxiliary fields in the
spin tensor sector.

The useful principle is now more precise: the energy, canonical
brackets, and constraint algebra must be derived from the same
microscopic reduction. Matching only the inverse propagator
suggested by an energy functional can invent a mode that the
actual reduction does not possess.

For this mediator proposal, a constructive continuation must find
a joint constraint system whose auxiliary contribution cancels
or consistently deforms (9), while deriving its reduced
symplectic form and retaining exactly two tensor modes. This
requires more than two independent electric sectors. A successful
construction would still need nonlinear refoliation consistency,
universal matter coupling, a stable microscopic state, and a
controlled Lorentzian continuum.

There is no general exclusion of gapless or gauge-charged mediators
here. Changing how auxiliaries transform can change the canonical
subspace assumed in (5); changing their brackets can change (9).
Neither change has been derived for the repository's finite spins.
The fixed-species matter curvature remainder and physical locality
targets also remain open. No Einstein phase or TOE is claimed.

## 8. Verification

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/constrained_mediator_audit.py

[The script](scripts/constrained_mediator_audit.py) produces
[the report](data/constrained_mediator_audit.json). It includes
exact symbolic brackets, reduced canonical coordinates, the
nilpotent physical flow, and the unstable mediator determinant,
plus 132 numerical cases:

- 96 complete auxiliary spectra, with mixed coordinate/momentum
  couplings and both massive and gapless auxiliary blocks.
- 12 periodic-lattice constrained electric minima, checked by
  independent least squares and transverse variations.
- 8 full Dirac-reduced evolutions of (10), retaining auxiliary outputs.
- 16 tensor-current bracket ranks, plus an exact finite-lattice
  contraction of previously frozen current patterns.

The general arguments are analytical. These calculations verify
normalization, signs, and reductions; they are not finite-spin
phase evidence. No Lean source is changed or theorem added.
