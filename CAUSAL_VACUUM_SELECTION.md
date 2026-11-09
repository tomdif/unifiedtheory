# Selecting the free tensor clock by vacuum stability and causal propagation

Date: 2026-09-11

**A conditional selection gap can be closed:** for the previously
constructed Gaussian tensor vacuum, a common cone of stable observers
and allowed propagation fixes the free Hamiltonian to the linear-wave
one. The cubic-wave Hamiltonian fails the observer-stability requirement
at arbitrarily small nonzero momentum. Neither the common cone nor
its microscopic realization has been derived. This is not a derivation
of nonlinear Einstein gravity or a completed TOE.

The organizing principle proposed here is: **the same local causal
structure governs both the observers for whom the vacuum is a ground
state and the propagation of its excitations.** It strengthens the
repository's local-clock proposal by giving a directly testable spectral
requirement. It is additional physics, not a consequence of a partial
order alone.

The relation between causality, positive energy and dispersion is
established physics. Bros and Epstein prove a substantially more general
Lorentz-invariance result for stable-particle dispersion under
microcausality and energy positivity in every Lorentz frame. The
elementary gapless argument below is a specialization and an application
to this repository, not a claim to have discovered that general result.
[Bros--Epstein, sections 1--2](https://arxiv.org/pdf/hep-th/0204118).

## 1. Modular data do not distinguish the two Hamiltonians

The [previous calculation](PROJECTED_TENSOR_VACUUM.md) found identical
nonzero-mode Gaussian vacua for

    H1 = (J/2) p^2 + (g/2) |k|^2 h^2,
    H3 = (J/2) |k|^2 p^2 + (g/2) |k|^4 h^2,
    W(k) = alpha |k|,       alpha = sqrt(g/J).             (1)

The displayed cubic coefficients use the same reference-length units
as that calculation. Frequencies are sqrt(Jg)|k| and sqrt(Jg)|k|^3.

For a fixed algebra A and a common cyclic, separating vector Omega,
the Tomita operator is specified by S(a Omega)=a* Omega. Its polar
decomposition therefore gives the same modular operator for both
Hamiltonians. At a tensor-factor regulator the simpler statement is
rho_R,1=rho_R,3, hence -log(rho_R,1)=-log(rho_R,3) on their common
support. No physical Hamiltonian occurs in either construction.

Thus even all modular data of the **same equal-time regional algebras**
cannot decide between (1). A proposed spacetime algebra transported by
H1 and one transported by H3 need not be the same net. Building such a
net, or requiring a geometric action of its modular groups, adds
dynamical compatibility conditions.

Modular covariance can reconstruct spacetime symmetries with its
stated algebraic and geometric hypotheses; these hypotheses are not
automatic properties of a finite-spin vacuum.
[Guido, sections 1--2](https://www.numdam.org/item/AIHPA_1995__63_4_383_0.pdf).
The defining modular construction is also reviewed in
[Kuckert, appendix A](https://arxiv.org/pdf/hep-th/0107236).

The audit illustrates this with finite harmonic rings and
L=m^2 I+the nearest-neighbor Laplacian, m>0:

    H_a = p^T p/2 + h^T L h/2,
    H_b = p^T L p/2 + h^T L^2 h/2.

Independent canonical diagonalizations give the same full covariance,
the same reduced modular Hamiltonian, and different mode frequencies.
The small mass regulates the homogeneous mode. These rings are
oscillator examples, not finite-spin graviton phases. Gaussian
correlation methods for regional entanglement Hamiltonians are standard;
see [Eisler et al.](https://arxiv.org/abs/2007.01804).

Physical TT Fourier variables do not factor into local spatial
subsystems: their transverse projectors are nonlocal. We do not
interpret a partial trace over TT modes as a gravitational half-space
algebra.

## 2. Vacuum stability supplies a lower energy bound

Suppose a homogeneous limiting theory has strongly commuting
translation generators H,P, a vacuum with H Omega=P Omega=0,
and a compact convex symmetric set V of velocities containing zero
in its interior. Define its support function

    s_V(k) = sup_(v in V) v.k.                            (2)

Require the vacuum to remain a ground state for every tilted
translation generator

    H_v = H - v.P,       v in interior(V).                (3)

This convention differs by v -> -v from some frame conventions.
A positive overall time-calibration factor does not affect positivity.
Neither a unitary boost symmetry nor a Lorentz transformation law
for fields is assumed in this elementary test.

The joint spectral theorem gives

    H_v >= 0 for all v in interior(V)
      iff every spectral point (E,k) obeys E >= s_V(k).   (4)

The proof is the intersection of the half-spaces E-v.k>=0;
continuity extends the supremum to the boundary. For a spherical
velocity set of radius c, (4) reads E>=c|k|.

The ground-state hypothesis in (3) is stronger than mere stationarity
of the vacuum. Calling a stationary state a vacuum does not establish
it. Related passivity formulations can derive the spectrum condition
under their assumptions; [Kuckert, proposition 5.1](https://arxiv.org/pdf/hep-th/0107236).
Here (3) is explicit, so the proof needs no passivity theorem.

For free bosons with E(k)=gamma |k|^3, take k parallel to any nonzero
v and sufficiently small. Then

    E(k)-v.k = |k| (gamma |k|^2-|v|) < 0.                (5)

Even one excitation disproves (3). In the ideal bosonic Fock model,
arbitrary occupation of that mode makes H_v unbounded below.
This does not make H3 unstable in its rest frame; H3 remains positive.
It also does not establish unbounded energy in a finite spin system,
whose actual Gaussian phase has not been proved.

More generally, a stable branch E(k)=O(|k|^z), z>1, cannot meet
(3) for any size-independent open velocity neighborhood. If the
shared-vacuum family has E(k)=sqrt(Jg)|k| f(|k|^2), with f analytic,
nonnegative and finite near zero, such a neighborhood requires f(0)>0.
This selects a nonzero linear leading term, but does not alone fix its
speed or remove higher-order corrections.

## 3. A common propagation cone fixes a gapless dispersion

**Conditional cone theorem.** In a star-shaped momentum neighborhood
of zero, let a stable excitation branch E(k) be continuous with E(0)=0
and differentiable away from zero. Assume (4) and

    grad_k E(k) in V.                                    (6)

Then

    E(k) = s_V(k).                                       (7)

To prove the upper bound, integrate on the radial segment:

    E(k) = integral_0^1 grad E(t k).k dt
         <= integral_0^1 s_V(k) dt = s_V(k).

One may first integrate from epsilon to one and take epsilon -> 0.
The compactness of V bounds the derivative and justifies this limit.
Equation (4) supplies the reverse inequality. No expansion in k
or rotationally invariant Hamiltonian ansatz is needed.

For V={v: |v|<=c}, every such branch has E(k)=c|k|. Thus
different speeds for two gapless species are incompatible with the
two requirements for the same V: a slower species violates (4),
and a faster one violates (6). A massive branch has E(0)>0 and
is outside this elementary argument.

The meaning of (6) must be respected. It is a condition on a real,
stable dispersion branch. It is a necessary consequence of
microcausality in the relevant local-field setting, not a sufficient
test of microcausality. Damped peaks and broad resonances do not
automatically satisfy this group-velocity bound. See
[Bros--Epstein, section 1](https://arxiv.org/pdf/hep-th/0204118) and the
explicit stable-pole discussion in
[Hui et al., section 5.2](https://arxiv.org/html/2502.04215v2#S5.SS2).
For this application, one must establish suitable local observables
with overlap on the tensor pole. The TT metric itself is not a
local canonical field algebra on space.

The two hypotheses have independent content. E=ck/2 respects the
group bound but fails energy positivity for some |v|<c.
E=2ck has positive tilted energy throughout that cone but violates
the group bound. The same distinction applies to
E=ck(1-beta k^2) and E=ck(1+beta k^2) on a small momentum interval.
Testing only one side cannot select the common wave dynamics.

## 4. Applying the theorem fixes the quadratic tensor Hamiltonian

Keep the supplied canonical nonzero-mode TT sector, with two
polarizations, and its pure Gaussian vacuum of precision
W(k)=alpha |k| I_2. On the associated oscillator Fock space let H
be a positive, translation-invariant quadratic Hamiltonian with
this exact vacuum. Subtract its vacuum energy.

Its creation and annihilation operators are fixed by that state:

    a_k = sqrt(alpha |k|/2) h_k
                     + i p_k/sqrt(2 alpha |k|).          (8)

Here real fields obey the usual k,-k adjoint relations. An arbitrary
quadratic Hamiltonian can contain a* M a and pair creation/annihilation.
The pair-creation term acting on the vacuum is a two-particle vector;
for the vacuum to be an eigenvector it must vanish. Hermiticity
also removes the pair-annihilation term. Thus

    H = integral a_k^* M(k) a_k,       M(k)=M(k)^*>=0.    (9)

This argument is at the regulated quadratic level; a continuum
version needs the usual operator domains. It excludes interactions
and additional sectors by hypothesis, rather than silently ignoring
them. The eigenvalues of M(k) are the two excitation energies.

If both branches satisfy the cone theorem for the ball of radius c,
both eigenvalues equal c|k|. A Hermitian matrix with just that
eigenvalue is c|k| I_2, so (9) uniquely gives

    H_selected =
      (1/2) integral [(c/alpha) p_TT^2
                         + c alpha |k|^2 h_TT^2],       (10)

up to the subtracted constant. Its Euclidean metric response is

    G_TT(omega_E,k) =
      (c/alpha) I_2 / (omega_E^2+c^2 |k|^2).             (11)

The result fixes the residue as well as the frequency, because the
state fixes alpha and the canonical brackets are retained.
For c=sqrt(Jg), (10) is exactly H1 in (1). The
[prepotential bridge](PREPOTENTIAL_LATTICE_BRIDGE.md) already gives
a consistent constrained linear-gravity realization of this reduced
Hamiltonian. No new bracket is assigned here.

This is the selection step that state matching alone was missing.
Its hypotheses have not been supplied by the compact tensor spin
Hamiltonian. Within that model's regular local neutral quadratic
class, the [existing derivative bound](COMPACT_TENSOR_DYNAMICS.md)
forces E=O(|k|^3). Consequently that entire specified class fails
(3). Adding the principle does not transform its Hamiltonian;
a successful microscopic construction must leave at least one
assumption of that restricted class.

## 5. A cone need not be a Lorentz metric

The theorem also works for an ellipsoid

    V={v: v^T D^(-1) v<=1},       D>0.

Then s_V(k)=sqrt(k^T D k), the acoustic metric already encountered
in the repository. But a general V need not be an ellipsoid.
For the unit l4 velocity ball,

    s_V(k) = ||k||_(4/3),
    ||grad s_V(k)||_4 = 1 for k != 0.                    (12)

This dispersion satisfies (4) and (6), yet its square is not a
quadratic form. For coordinate unit vectors e1,e2, its
parallelogram defect is 4 sqrt(2)-4, rather than zero.
This is a counterexample to inferring a Lorentz metric from the
cone theorem alone. It is a dispersion-level example, not a
construction of a local quantum theory with that cone.

A spherical or ellipsoidal cone, the dimension of space, and local
translation structure still need microscopic suppliers. A bare
partial order does not supply these differentiable structures,
the spectrum condition, or the common physical observable net.

## 6. Finite-size and approximate versions give measurable targets

For the one-dimensional momentum slice of the staggered regulator,
let q(k)=2 sin(k/2), 0<k<=kappa<1. The cubic branch has

    v_crit(L)=min_k sqrt(Jg) q(k)^3/k
            =sqrt(Jg) [2 sin(pi/L)]^3/(2 pi/L)
            ~sqrt(Jg) (2 pi/L)^2.                       (13)

The equality holds on this low-momentum window when it contains
the first nonzero mode: q(k)^3/k is increasing there.
An axial sequence alone suffices to rule out a positive uniform
cone in higher dimensions. Continuous translations and H-vP on
a lattice are spectral diagnostics for a proposed limit, not
an assertion of microscopic continuous boost symmetry.

For the linear lattice branch, throughout that window

    sqrt(Jg)(1-kappa^2/24) <= E1(k)/k <= sqrt(Jg),
    |dE1/dk| <= sqrt(Jg).                                (14)

Thus its continuum discrepancy is controlled as kappa -> 0.
A finite lattice does not satisfy an exact continuum light cone
merely because its interactions have finite range.

There is also a useful stability estimate. Suppose on radial
segments down to zero, for 0<=delta<1,

    E(k)>= (1-delta)c|k|,
    hat(k).grad E(k)<= (1+delta)c.                       (15)

The same integral proof gives

    (1-delta)c|k| <= E(k) <= (1+delta)c|k|.              (16)

For a real independent Gaussian polarization of unchanged
precision alpha |k|, put f=E/(c|k|). Its response relative to
(11), at s=omega_E/(c|k|), is

    G/G_selected = f(s^2+1)/(s^2+f^2),
    |G/G_selected-1| <= delta/(1-delta).                 (17)

The ratio lies between f and 1/f. This is uniform in Euclidean
frequency, including zero; it is not a theorem for a broadened
interacting spectral function.

At finite size, an additive error bound H_v>=-epsilon_L on the
tested one-excitation sector only yields
E(k)>=c|k|-epsilon_L. To get a vanishing relative error at
k_min=2 pi/L, one needs epsilon_L/k_min -> 0. An error tending
to zero without this scaling is insufficient. An upper estimate
also needs control of the omitted interval between zero and
k_min, or a separate bound there.

## 7. What is closed, and the next microscopic requirement

The free, canonical, two-polarization Gaussian selection problem
is closed **conditional on** (3), (6), a common spherical cone,
and the previously specified state. Modular matching by itself
is proved insufficient. This removes an ambiguity in the
proposed model; it does not prove the necessary microscopic
phase exists.

The next construction must produce a controlled local observable
limit and calibrated translations, establish vacuum positivity
under the corresponding tilted clocks uniformly in size, and
bound propagation in the same limiting cone. A viable tensor
phase must pass these tests on both polarizations with nonzero
local observable overlap. The regular compact neutral Gaussian
class already fails the positivity test, so another phase,
constraint realization, or controlled scaling limit is needed.

Even success would give the free tensor sector. Spatially
varying normal deformations and their full constraint algebra
are stronger than the constant translations tested here.
The [conditional Einstein constraint result](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
still needs its microscopic supplier. Nonlinear self-coupling,
universal matter coupling, homogeneous gravitational data,
fixed-species curvature control, Standard Model dynamics and
a physical TOE remain open.

## 8. Reproduction

Run the audit:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/causal_vacuum_selection_audit.py

The report records independent harmonic-ring ground-state and
regional modular reconstructions, finite-volume cubic stability
witnesses, dispersion tests that distinguish the two cone
conditions, anisotropic and non-ellipsoidal support functions,
and Gaussian response error bounds. All 68 numerical cases and
three exact identities pass. The maximum regional modular-matrix
discrepancy is 3.86e-10, and thermal reconstruction of the regional
covariance has error below 3.1e-15. The cubic spectral calculation
uses L=16 through 1024.

Numerical tests check these finite examples and identities; the
all-momentum selection argument is the analytical proof above.
No Lean source changes.
