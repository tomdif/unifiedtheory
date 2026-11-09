# A microscopic clock bracket and a controlled metric-dilation repair

Date: 2026-09-10

This tests the missing microscopic step in
[the conditional gravity derivation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md).
A stable spin-field model gives an exact local energy commutator whose
coefficient is a dynamical spin tensor. Its spatial transformation law
fails. A finite-dimensional obstruction explains why identifying a
bounded spin observable directly with the full metric cannot satisfy
that law uniformly on every state. A logarithmic metric variable repairs
one dilation generator in a controlled low-occupation limit.

The full gap is **not closed**: neither a stable gravitational phase nor
the complete metric-dependent constraint algebra follows. The new
results distinguish an exact microscopic commutator, a uniform stencil
estimate, a finite-dimensional obstruction, and a repaired single
generator from a derivation of Einstein gravity.

## 1. An explicit positive model with a dynamical spin stiffness

Use the six transitions of the four-spin cell. Write
`X_alpha=|alpha><Omega|+|Omega><alpha|`, alpha=0,...,5, and let E_alpha
be the complete Frobenius-orthonormal symmetric tensor basis. At each
cell define

```
C_s^ij=kappa delta^ij I+gamma sum_alpha E_alpha^ij X_s,alpha,
h_s=mu N_s+M(I-P_0-N_s),           mu,M>0.             (1)
```

N_s projects onto the six active excited states. The spin Hilbert space
still has dimension sixteen per cell. Different cells commute; tensor
components within a cell generally do not. The star-transition algebra
gives, for real vectors u,v,

```
||sum_ij u_i (C_s^ij-kappa delta^ij I) v_j||
 =|gamma| sqrt((|u|^2 |v|^2+(u.v)^2)/2)
 <=|gamma| |u| |v|.                                  (2)
```

In particular `u_i C_s^ij u_j >=(kappa-|gamma|)|u|^2 I`.
The tensor is dynamical: `[h_s,C_s^ij]` is generally nonzero.

On a supplied periodic carrier let Q_x,P_x be canonical scalar-field
coordinates, and D_i the centered difference with spacing a. The scalar
sector remains the canonical field supplied by the previous large-spin
construction; it is not replaced here by four-state matter qubits.
For any real lapse profile n define the local energy generator

```
H[n]=sum_s n_s [h_s+P_s^2/2+m_phi^2 Q_s^2/2
                      +(D_i Q)_s C_s^ij (D_j Q)_s/2]. (3)
```

There is one spin cell per field vertex; the choice of carrier and
local energy assignment are model inputs. The previous quintet hopping
is absent from this diagnostic extension. No gravitational constraint
is imposed by defining H[n]. These H[n] are newly specified local energy
generators; they have not been derived from the guarded history-clock
constraints in [the local causal clock](LOCAL_CAUSAL_CLOCK.md).

For kappa>|gamma| and m_phi>0,

```
H[1]>=sum_s [P_s^2+m_phi^2 Q_s^2]/2
                    +(kappa-|gamma|) sum_s |D Q_s|^2/2. (4)
```

Thus the full finite-volume matrix Schrodinger operator is bounded
below and confining, and has a ground state. This does not establish
uniqueness or an infinite-volume phase. Keeping m_phi>0 avoids discarding
the constant field coordinate: arbitrary local lapses do not preserve
the previous relative-field reduction. The mass drops out of the
commutator below. At m_phi=0 the energy lower bound remains, but the free
zero coordinates require separate treatment.

## 2. The local energy commutator is exact

Let n,m denote diagonal matrices of lapse samples. Define the
operator-valued field stiffness matrix

```
A[n]=sum_ij D_i^T diag_s(n_s C_s^ij) D_j+m_phi^2 n I_spin,
K[n,m]=m A[n]-n A[m].                                (5)
```

All statements below hold on the common Schwartz domain of the
canonical field operators tensored with the finite spin space.
Potential terms centered at distinct cells commute because their spin
supports differ and their field coordinates commute. At one cell the
two lapses multiply the very same potential operator, so its commutator
with itself vanishes even though its tensor components need not commute.
The mixed onsite-spin/potential commutators cancel with the symmetric
factor n_s m_s. Kinetic-kinetic commutators vanish. Canonical field
commutation therefore gives exactly

```
[H[n],H[m]]/i
 =1/2 sum_xy [P_x K[n,m]_xy Q_y+Q_y K[n,m]_xy P_x].    (6)
```

The mass contribution to K cancels since n and m commute. This is an
operator identity, not a ground-state or harmonic approximation of the
spin variables. It is an energy-current identity of the type appearing
in the [Dirac-Schwinger condition](https://journals.aps.org/pr/abstract/10.1103/PhysRev.158.1608).
The full covariance conditions of that literature are not inferred
from this one identity.

Formally replacing D_i by partial_i yields

```
K[n,m] Q = C^ij(n partial_i m-m partial_i n) partial_j Q.
```

This has the desired inverse-metric-shaped coefficient. It is still
only a candidate coefficient: the scalar kinetic density, volume
factor, and spatial action on C have not been shown to be those of a
common spacetime metric.

Density weights also matter. A canonical scalar coupled to a metric q
has coefficients `1/sqrt(det q)` and `sqrt(det q) q^ij` in its kinetic
and gradient terms. Absorbing the first into the lapse would identify
the gradient coefficient here with `(det q) q^ij`, a tensor density,
rather than q^ij itself. Its spatial Lie derivative includes a density
term and must be tested with the correspondingly weighted lapse.
Equation (6) alone does not choose either identification.

## 3. A uniform consistency bound needs no smooth spin configuration

The formal replacement has a stronger finite-stencil statement. Take
real smooth profiles n,m,f,g on a fixed torus, and form the coefficient
bilinear `a^3 f^T K[n,m] g`. Discrete integration by parts gives

```
a^3 f^T K[n,m] g
 =a^3 sum_sij [n_s D_i(m f)_s-m_s D_i(n f)_s] C_s^ij D_j g_s. (7)
```

The target quadrature is
`a^3 sum_sij f_s(n partial_i m-m partial_i n)_s C_s^ij partial_j g_s`.
This compares coefficient forms, not the operator norm of unbounded
field energy generators.

Centered differentiation has error
`|D_i F-partial_i F|<=a^2 ||partial_i^3 F||_infinity/6`.
Let e_0 bound the Euclidean norm of the vector with components
`(||n|| ||partial_i^3(mf)||+||m|| ||partial_i^3(nf)||)/6`;
let d_0 bound the norm of `||partial_i^3 g||/6`, g_0 bound |grad g|,
and F_0 bound `|f(n grad m-m grad n)|`. Using (2), the operator-norm
error in (7) is at most

```
Vol (kappa+|gamma|) a^2 [e_0(g_0+a^2 d_0)+F_0 d_0].  (8)
```

The constant is independent of the number or state of the spin cells.
No spatial derivative of C occurs. It does not prove that the sequence
of operator fields C_a has a smooth or state-independent continuum
limit, nor that the field response has a gravitational pole.

For this star-transition model the audit can compute the exact norm
of the coefficient-form error without constructing a huge tensor
product. Write its local contributions as
`c_s I+sum_alpha v_s,alpha X_s,alpha`. Independent cells commute and
each star has extreme eigenvalues +/-|v_s|, hence the total norm is
`|sum_s c_s|+sum_s |v_s|`. The numerical stencil check therefore tests
the full spin-space coefficient norm, not a sampled expectation value.

## 4. Why the first bracket does not establish gravity

For an externally specified classical vector field xi, the matter
momentum generator D_m[xi], constructed from P and Q, commutes with
every C_s. If C were an inverse spatial metric, the required
transformation would instead be

```
delta_xi C^ij=xi^k partial_k C^ij
                         -C^ik partial_k xi^j-C^jk partial_k xi^i. (9)
```

At a point where xi=0 and partial_i xi^j=sigma delta_i^j, this is
`delta C^ij=-2sigma C^ij`, not zero. Such a vector field can be chosen
smoothly in a coordinate neighborhood; no global torus dilation is
assumed. Extending (6) using this matter generator for prescribed xi
therefore fails the metric transformation law. The missing geometric
part is a real algebra gap. In (6) itself the effective shift contains
C: because finite-cell C components need not commute with one another,
that composite operator can act nontrivially on C. This extra action
does not construct an independent spatial generator or prove (9).
The local energies also have not been made into first-class constraints.
For the alternative density `(det q) q^ij`, the same local dilation
would give `+4sigma C^ij` in three dimensions, again incompatible with
the zero action of D_m. Changing the density convention does not
remove the missing geometric generator.

Even allowing an arbitrary finite-dimensional self-adjoint generator G
cannot realize this dilation uniformly on the full microscopic space.
For any positive matrix C and nonzero real sigma, choose a normalized
eigenvector at its largest eigenvalue. Its expectation of i[G,C] is
zero. Consequently

```
||i[G,C]+2sigma C|| >=2|sigma| ||C||.                (10)
```

The bound is sharp: G=0 attains it. For the diagonal component of (1),
`||C^ii||=kappa+|gamma|`, so increasing the Hilbert-space dimension
alone cannot make a full-space norm error vanish at fixed parameters.
Equivalently, unitary conjugation preserves ||C||, whereas finite
dilation multiplies it by exp(-2sigma t).

This is a finite/full-space obstruction, not a no-go theorem for
emergent gravity. A growing low-occupation domain need not be invariant
under a gauge generator or metric operator. Taking that limit changes
the premise behind (10), as the following explicit repair illustrates.

## 5. A logarithmic metric repairs one generator on a controlled domain

Use R copies of the vacuum and second-singlet pair inside a symmetric
spin block. Its occupation states are |n>, n=0,...,R. The collective
transition B_R^dagger acts by
`sqrt((n+1)(1-n/R))`. Define the finite dressing

```
a_R^dagger=B_R^dagger f_R(N),
f_R(n)=(1-n/R)^(-1/2) for n<R,       f_R(R)=0.
```

This is exactly the truncated oscillator creation matrix, with
coefficient sqrt(n+1) below the top state. All operators remain
explicit finite matrices on a symmetric subspace of microscopic spins.
The dressing and the symmetric block are new model choices; selecting
that block as a stable phase is not proved.

Set d=R+1 and define, for a fixed scale ell>0,

```
Q_R=(a_R+a_R^dagger)/sqrt(2),
P_R=(a_R-a_R^dagger)/(i sqrt(2)),
h_R=ell Q_R,           C_R=kappa exp(-h_R),
G_R=2sigma P_R/ell.                                  (11)
```

C_R is strictly positive. It represents one inverse-metric dilation
component, not all six spatial metric components. The exact truncated
commutator is `[Q_R,P_R]=i(I-d|R><R|)`. The derivative formula for the
matrix exponential therefore gives

```
E_R:=i[G_R,C_R]+2sigma C_R
 =2sigma kappa d integral_0^1 exp[-(1-s)ell Q_R]
                         |R><R| exp[-s ell Q_R] ds.   (12)
```

Let P_<=n project onto a fixed occupation cutoff n<R. Q_R changes
occupation by one and ||Q_R||<=sqrt(2R). Put
`x=ell sqrt(2R)` and `L=R-n`. In the exponential series, connecting
the top state to this input sector requires at least L powers. Thus,
uniformly for 0<=s<=1,

```
||P_<=n exp(-s ell Q_R)|R>|| <= exp(x) x^L/L! =:T_R,
||P_<=n E_R P_<=n|| <=2|sigma| kappa(R+1) T_R^2.      (13)
```

There is also a stronger estimate retaining every output component.
Using `||exp[-(1-s)ell Q_R]||<=exp(x)` on the other side of (12) gives

```
||E_R P_<=n|| <=2|sigma| kappa(R+1) exp(x) T_R.       (14)
```

For fixed n and ell both bounds tend to zero: Stirling's bound gives
`log T_R=-(R/2)log R+O(R)`. Thus the result concerns the full action
on the input domain, not just matrix elements within that domain.
The full-space error still obeys (10), and generally grows. Restriction
is performed after the full commutator, not before; the low-occupation
sector is not invariant under G_R. There is no contradiction with the
finite-dimensional bound.

These matrices have a consistent infinite-oscillator target under the
embeddings `|n>_R -> |n>` into a common Fock space. On each fixed input
cutoff, `Q_R^k` agrees with `Q^k` once R>=n+k, and uniformly in R

```
||Q_R^k P_<=n|| <=sqrt(2^k (n+k)!/n!).               (15)
```

The exponential series obtained by multiplying this bound by
`ell^k/k!` is summable. Dominated convergence therefore gives
`C_R P_<=n -> kappa exp(-ell Q) P_<=n` in operator norm from this
fixed finite input space to Fock space. The target is a positive,
unbounded operator, and `G_R P_<=n` eventually equals
`(2sigma/ell) P P_<=n`. Equation (14) controls the infinitesimal
dilation defect. No finite-time evolution or physical-sector
invariance is inferred from this domain statement.

An explicit bound for that metric convergence is
`2kappa sum_{k>=R-n+1} ell^k sqrt(2^k(n+k)!/n!)/k!`.
Successive summands have decreasing ratio
`ell sqrt(2(n+k+1))/(k+1)`; once it is below one, the tail is bounded
by the first summand divided by one minus that ratio. The audit
compares the finite matrix with independent normal-ordered oscillator
matrix elements and reports this bound, which also covers the omitted
output occupations in the common Fock space.

This closes one precise subproblem: a positive metric component and
its dilation action can arise as a controlled limit of finite spin
matrices. It does not prove the full spatial Lie action, a metric
canonical phase space, or the normal-deformation brackets of GR.

## 6. What the model must now change

The direct bounded identification C=kappa I+gamma X is useful as a
stable strain coefficient and yields the exact first clock bracket.
It cannot supply unrestricted metric transformations in full-space
operator norm. The revised target uses collective logarithmic metric
coordinates with a growing approximation domain. Even this requires
care: each finite block has bounded metric spectrum, the dressing can
act on the whole block, and no uniform microscopic interaction range
or symmetric-sector ground-state selection has been proved as R grows.

The remaining tasks are the complete six-component canonical and
spatial algebra, its normal-deformation generator, a stable physical
sector, matter sources, and a controlled quantum continuum with two
gravitational poles. This note establishes none of those by assuming
Einstein's Hamiltonian. The full gravitational gap remains open.

## 7. Verification

The [audit](scripts/spin_clock_bracket_audit.py) and its
[report](data/spin_clock_bracket_audit.json) check the exact finite spin
tensor, the full spin-field commutator on a low-occupation input domain
with sufficient intermediate oscillator levels, the volume-independent
coefficient estimate, the finite dilation obstruction, and the
logarithmic repair. The [Lean module](UnifiedTheory/Audit/KFCausalSpinClockBracket.lean)
provides twelve supporting matrix and scalar algebra results, all using
only the standard Lean axioms. It does not formalize the complete
operator identity or the convergence theorem. General domain,
confinement, and exponential-tail arguments remain analytical suppliers.

The finite energy-bracket audit uses three field sites, one dynamical
sixteen-state spin cell, and two supplied algebraic stencils to include
noncommuting tensor components. It compares all output rows in dimension
1,344 on 160 input states, with enough intermediate oscillator levels;
the largest residual in six lapse pairs is below `1.36e-14`. The generic
all-cell commutator is established by the analytical cancellation
argument, not by enumerating the many-cell spin Hilbert space.

The coefficient-norm audit uses four cubic grids, from 729 to 274,625
spin cells. Its errors divided by a^2 approach 0.62 for the specified
profiles and satisfy (8) at every size. Thirty arbitrary Hermitian
generators satisfy the sharp full-space dilation bound 0.54 at the
specified parameters; the zero generator attains it.

For ell=0.4, kappa=0.25, sigma=1 and input occupation at most two, the
measured full-output dilation defects at R=4,8,12,16 are respectively
`0.1234`, `6.85e-5`, `8.68e-9`, and `4.62e-13`. Larger blocks reach
floating-point roundoff. Eight block sizes through R=64 check the
Duhamel identity, the factorial bounds, and independent normal-ordered
metric matrix elements. Bounds below roundoff are consequences of the
analytical estimates, not numerically resolved measurements. Compressing
the generators before taking the commutator instead leaves an error
about 1.70, confirming why the common input-domain convention matters.

The integrated repository build passes all 8,952 jobs. The previous
136 frozen files remain unchanged, and all 266 source references across
33 audit reports verify against their recorded hashes.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/spin_clock_bracket_audit.py
lake env lean UnifiedTheory/Audit/KFCausalSpinClockBracket.lean
```
